#!/usr/bin/env python3
"""What the pull-request lifecycle labels mean, in one place.

Both the statistics charts and the pipeline-health report ask questions of the
same label timelines, and the answers have to agree. They very nearly did not:
the two disagreed by nineteen hours on how long one pull request had been
waiting, because one of them treated a `ci-failed` to `awaiting-author` swap as
the start of a fresh wait and the other did not.

The rules that matter, and that no caller should have to reimplement:

* `ci-failed` and `awaiting-author` are one state for timing purposes. The author
  reads a build log for one and review threads for the other, but the ball is in
  their court either way, so swapping one for the other continues the spell
  rather than beginning a new one.
* `awaiting-review` and `review-in-progress` are likewise one state. The pipeline
  swaps them while a round is judged and can restore the first afterwards, so
  counting label applications would split one cycle into several.
* Anything else ends a spell. A push that sends a pull request back to
  `awaiting-CI` is a genuinely fresh wait even if it fails again immediately.
"""

from __future__ import annotations

from datetime import datetime, timezone

STATE_REVIEW = {"awaiting-review", "review-in-progress"}
# The two states that put the ball in the author's court.
STATE_AUTHOR_ACTION = {"awaiting-author", "ci-failed"}
STATE_LABELS = {*STATE_AUTHOR_ACTION, *STATE_REVIEW}
# States in which the pull request has left the review queue: the author owns it,
# or CI is judging a new commit before review resumes.
STATE_AUTHOR = {*STATE_AUTHOR_ACTION, "awaiting-CI"}
LIFECYCLE_LABELS = {*STATE_REVIEW, *STATE_AUTHOR, "ready-to-merge"}
# The lifecycle-label workflow first landed on 2026-07-22. A pull request closed
# before that UTC day cannot contain one of its label events.
LIFECYCLE_EPOCH = datetime(2026, 7, 22, tzinfo=timezone.utc)

# In pipeline order, which is also the order to read them in: a stage is only
# the bottleneck if the ones feeding it are keeping up.
STAGE_ORDER = [
    "awaiting-CI",
    "awaiting-review",
    "review-in-progress",
    "ready-to-merge",
    "ci-failed",
    "awaiting-author",
]


def parse_dt(value: str | None) -> datetime | None:
    return datetime.fromisoformat(value.replace("Z", "+00:00")) if value else None


def iso_z(value: datetime) -> str:
    return value.astimezone(timezone.utc).isoformat().replace("+00:00", "Z")


def events(pr: dict) -> list[dict]:
    return sorted(pr.get("labeled_events") or [], key=lambda item: item["created_at"])


def latest_lifecycle_label(pr: dict) -> str | None:
    found = [event for event in events(pr) if event["label"] in LIFECYCLE_LABELS]
    return found[-1]["label"] if found else None


def current_stage(pr: dict) -> str | None:
    """The stage a pull request is in now, from the labels it currently carries.

    Not from the last timeline event: a pull request whose lifecycle label was
    removed has left that stage, and one with no events at all is still
    somewhere. The labels are what the pipeline actually maintains.
    """
    present = [label for label in pr.get("labels") or [] if label in LIFECYCLE_LABELS]
    return present[0] if len(present) == 1 else None


def author_episode_start(pr: dict) -> datetime | None:
    """When the current spell of waiting on the author began, or None."""
    start = None
    for event in events(pr):
        if event["label"] in STATE_AUTHOR_ACTION:
            if start is None:
                start = parse_dt(event["created_at"])
        elif event["label"] in LIFECYCLE_LABELS:
            start = None
    return start


def review_cycle_starts(pr: dict) -> list[datetime]:
    """When each review cycle began.

    A cycle begins where the pull request *enters* the review states from an
    author or CI state, or from no state at all, and lasts until it leaves for
    one. Consecutive review labels stay inside the same cycle. A bare removal,
    as on merge, never opens a cycle.
    """
    starts = []
    in_review = False
    for event in events(pr):
        if event["label"] in STATE_REVIEW:
            if not in_review:
                starts.append(parse_dt(event["created_at"]))
            in_review = True
        elif event["label"] in STATE_AUTHOR:
            in_review = False
    return starts


def episodes(pr: dict, now: datetime):
    """Yield (state, entered, left) for each spell, with the joining rules applied.

    `state` is the label the spell began in. A spell that is still running has
    `left` of None. This is the primitive both the queue-age histograms and the
    per-stage rates are built on, so that "how long has this been waiting" has
    exactly one answer.
    """
    timeline = [
        (parse_dt(event["created_at"]), event["label"])
        for event in events(pr) if event["label"] in LIFECYCLE_LABELS
    ]
    if not timeline:
        return

    def joined(previous: str, nxt: str) -> bool:
        return (
            (previous in STATE_AUTHOR_ACTION and nxt in STATE_AUTHOR_ACTION)
            or (previous in STATE_REVIEW and nxt in STATE_REVIEW)
        )

    spell_start, spell_label = timeline[0]
    for index in range(1, len(timeline)):
        at, label = timeline[index]
        if joined(spell_label, label):
            # Same spell continuing under a sibling label; the clock keeps running.
            spell_label = label
            continue
        yield spell_label, spell_start, at
        spell_start, spell_label = at, label

    if pr["state"] == "OPEN":
        yield spell_label, spell_start, None
    else:
        closed = parse_dt(pr.get("merged_at") or pr.get("closed_at"))
        yield spell_label, spell_start, closed or now


def waiting_since(pr: dict) -> datetime | None:
    """When the pull request's current spell began, whatever state it is in."""
    timeline = list(episodes(pr, datetime.now(timezone.utc)))
    if timeline and timeline[-1][2] is None:
        return timeline[-1][1]
    return None
