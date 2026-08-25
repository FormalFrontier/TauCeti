#!/usr/bin/env python3
"""Where is the pull-request pipeline slow right now, and why?

Merge throughput is one number at the end of a queue, so a fall in it says
something is wrong without saying what. This measures each stage separately:
how fast pull requests arrive at it, how fast they leave, how deep it currently
is, and how long they sit in it, each against a trailing baseline.

The stages are the lifecycle labels, which the pipeline maintains one at a time:

  awaiting-CI          waiting for a build on the latest commit
  awaiting-review      green, waiting for a reviewer
  review-in-progress   a review is running on this commit
  ci-failed            build failed; the author has to act
  awaiting-author      changes requested; the author has to act
  ready-to-merge       approved and green; waiting to merge

Two of those are not the project's to fix. `ci-failed` and `awaiting-author`
sit with the contributor, and reading a backlog there as a project problem
would point effort at exactly the wrong place, so they are reported separately
from the stages the project owns.

Data comes from the same snapshot the statistics charts use, so this needs no
new API surface and can be replayed offline:

    scripts/pipeline_health.py                       # fetch and report
    scripts/pipeline_health.py --json                # machine-readable
    scripts/pr_stats_graphs.py --dump-data snap.json --out-dir /tmp/x
    scripts/pipeline_health.py --data snap.json      # replay, no network
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from pr_lifecycle import (  # noqa: E402
    LIFECYCLE_EPOCH,
    STAGE_ORDER,
    STATE_AUTHOR_ACTION,
    current_stage,
    label_intervals,
    waiting_since,
    iso_z,
    parse_dt,
)
from pr_stats_graphs import atomic_write, fetch_snapshot, percentile  # noqa: E402

OWNED_BY_PROJECT = [s for s in STAGE_ORDER if s not in STATE_AUTHOR_ACTION]


def rate(count: int, hours: float) -> float:
    return count / hours if hours > 0 else 0.0


def observable_hours(start: datetime, end: datetime) -> float:
    """Hours of the interval in which lifecycle labels could exist at all.

    The labels landed on LIFECYCLE_EPOCH, so a window reaching back before it
    contains time in which no event could have been recorded. Dividing by the
    requested duration rather than the observable one understates every rate on
    a wide baseline.
    """
    start = max(start, LIFECYCLE_EPOCH)
    return max((end - start).total_seconds() / 3600, 0.0)


def analyse(
    snapshot: dict,
    window_hours: float,
    baseline_hours: float,
    now: datetime | None = None,
) -> dict:
    if window_hours <= 0 or baseline_hours <= 0:
        raise ValueError("window and baseline must be positive")

    # Replaying a snapshot must measure it as it was, not as though it were
    # taken now: otherwise every open interval gains however long the file has
    # been sitting on disk, and every recent rate reads as zero.
    if now is None:
        now = parse_dt(snapshot.get("fetched_at")) or datetime.now(timezone.utc)
    now = now.astimezone(timezone.utc)

    prs = snapshot["prs"]
    window_start = now - timedelta(hours=window_hours)
    # Disjoint, so the baseline is something to compare against rather than
    # something the recent window is already part of.
    baseline_end = window_start
    baseline_start = baseline_end - timedelta(hours=baseline_hours)
    window_span = observable_hours(window_start, now)
    baseline_span = observable_hours(baseline_start, baseline_end)

    entered = defaultdict(lambda: {"window": 0, "baseline": 0})
    left = defaultdict(lambda: {"window": 0, "baseline": 0})
    dwell = defaultdict(lambda: {"window": [], "baseline": []})
    depth: defaultdict[str, int] = defaultdict(int)
    oldest: dict[str, float] = {}
    unlabelled_open = 0

    for pr in prs:
        if pr["state"] == "OPEN" and not pr["is_draft"]:
            stage = current_stage(pr)
            if stage is None:
                unlabelled_open += 1
            else:
                depth[stage] += 1
                # How long this pull request has been waiting is a question
                # about its spell, not about the label currently on it: the
                # clock does not restart when the pipeline swaps a label for
                # its sibling. Rates below are the opposite, and use the atomic
                # per-label intervals.
                began = waiting_since(pr, now)
                if began:
                    waiting = (now - began).total_seconds() / 3600
                    oldest[stage] = max(oldest.get(stage, 0.0), waiting)

        for label, start, end in label_intervals(pr, now):
            if baseline_start <= start < baseline_end:
                entered[label]["baseline"] += 1
            if start >= window_start:
                entered[label]["window"] += 1

            if end is None:
                # Still running, so not a completed dwell: counting it would
                # bias a stuck stage's median downwards.
                continue

            hours = (end - start).total_seconds() / 3600
            if baseline_start <= end < baseline_end:
                left[label]["baseline"] += 1
                dwell[label]["baseline"].append(hours)
            if end >= window_start:
                left[label]["window"] += 1
                dwell[label]["window"].append(hours)

    def counted(field: str, start: datetime, end: datetime) -> int:
        return sum(
            1 for pr in prs
            if pr.get(field) and start <= parse_dt(pr[field]) < end
        )

    stages = []
    for label in STAGE_ORDER:
        stages.append({
            "stage": label,
            "owned_by_project": label not in STATE_AUTHOR_ACTION,
            "depth": depth[label],
            "oldest_waiting_hours": oldest.get(label, 0.0),
            "entered_per_hour": rate(entered[label]["window"], window_span),
            "left_per_hour": rate(left[label]["window"], window_span),
            "baseline_entered_per_hour": rate(entered[label]["baseline"], baseline_span),
            "baseline_left_per_hour": rate(left[label]["baseline"], baseline_span),
            "left_count": left[label]["window"],
            "baseline_left_count": left[label]["baseline"],
            "median_dwell_hours": percentile(dwell[label]["window"], 0.5),
            "baseline_median_dwell_hours": percentile(dwell[label]["baseline"], 0.5),
        })

    result = {
        "schema_version": 1,
        "repo": snapshot.get("repo"),
        "generated_at": iso_z(now),
        "snapshot_fetched_at": snapshot.get("fetched_at"),
        "window_hours": window_hours,
        "baseline_hours": baseline_hours,
        "observable_window_hours": window_span,
        "observable_baseline_hours": baseline_span,
        "opened_per_hour": rate(counted("created_at", window_start, now), window_span),
        "baseline_opened_per_hour": rate(
            counted("created_at", baseline_start, baseline_end), baseline_span),
        "merged_per_hour": rate(counted("merged_at", window_start, now), window_span),
        "baseline_merged_per_hour": rate(
            counted("merged_at", baseline_start, baseline_end), baseline_span),
        "merged_count": counted("merged_at", window_start, now),
        "baseline_merged_count": counted("merged_at", baseline_start, baseline_end),
        "opened_count": counted("created_at", window_start, now),
        "baseline_opened_count": counted("created_at", baseline_start, baseline_end),
        "open_prs": sum(1 for pr in prs if pr["state"] == "OPEN"),
        "open_prs_without_a_lifecycle_label": unlabelled_open,
        "stages": stages,
    }
    result["anomalies"] = anomalies(result)
    result["cause"] = find_cause(result)
    return result


ROUND_TO = 2


def rounded(result: dict) -> dict:
    """Round for output only.

    Comparisons run on the raw values: rounding first turns one event in a
    fortnight into a rate of exactly zero, which silently changes which branch
    every threshold takes.
    """
    def fix(value):
        return round(value, ROUND_TO) if isinstance(value, float) else value

    out = {k: fix(v) for k, v in result.items() if k not in ("stages", "anomalies")}
    out["stages"] = [{k: fix(v) for k, v in stage.items()} for stage in result["stages"]]
    out["anomalies"] = [{k: fix(v) for k, v in a.items()} for a in result.get("anomalies") or []]
    return out


# A stage must clear one of these to be blamed at all. Without them the search
# always returns something, and a heuristic that always finds a culprit is not a
# diagnosis.
MIN_COMPLETIONS = 3          # below this a median dwell is noise
GROWTH_PER_HOUR = 0.05       # arrivals must outpace departures by a real margin
SLOWDOWN_FACTOR = 2.0        # the oldest occupant, against normal dwell
THROUGHPUT_FRACTION = 0.75   # of baseline, below which something is wrong


def anomalies(result: dict) -> list[dict]:
    """Every project-owned stage misbehaving, worst first.

    A pipeline can have more than one thing wrong with it, and on real data it
    usually does: naming a single culprit hid a stage full of approved work that
    was not merging, because a different stage happened to be filling faster.
    """
    found = []
    for stage in result["stages"]:
        if not stage["owned_by_project"] or not stage["depth"]:
            continue
        growth = stage["entered_per_hour"] - stage["left_per_hour"]
        normal = stage["baseline_median_dwell_hours"]
        enough = stage["baseline_left_count"] >= MIN_COMPLETIONS
        slowdown = (
            stage["oldest_waiting_hours"] / normal
            if enough and normal and stage["oldest_waiting_hours"] else 0.0
        )
        filling = growth > GROWTH_PER_HOUR
        stalled = slowdown >= SLOWDOWN_FACTOR
        if not (filling or stalled):
            continue
        reasons = []
        if filling:
            reasons.append(
                f"arriving at {stage['entered_per_hour']:.2f}/h and leaving at "
                f"{stage['left_per_hour']:.2f}/h, so it is filling faster than it drains"
            )
        if stalled:
            reasons.append(
                f"its oldest has waited {stage['oldest_waiting_hours']:.0f}h against a "
                f"{normal:.1f}h normal dwell"
            )
        found.append({
            "stage": stage["stage"],
            "depth": stage["depth"],
            "growth_per_hour": growth,
            "slowdown_factor": slowdown,
            "why": "; ".join(reasons),
        })
    # Filling beats merely stalled, then by how fast, then by how far past normal.
    found.sort(key=lambda item: (item["growth_per_hour"] > GROWTH_PER_HOUR,
                                 item["growth_per_hour"], item["slowdown_factor"]),
               reverse=True)
    return found


def find_cause(result: dict) -> dict | None:
    """Why throughput is down, when it is.

    Fewer merges can mean the queue is stuck or simply that less went into it,
    and those want opposite responses: adding review capacity does nothing about
    a week when nobody opened anything. Both are answers, so both are reported.
    Only when neither holds is the fall genuinely unexplained, and saying so is
    better than picking a stage to blame.
    """
    baseline = result["baseline_merged_per_hour"]
    if not baseline or result["baseline_merged_count"] < MIN_COMPLETIONS:
        # Nothing to compare against. Saying "healthy" here would be a guess
        # dressed as a finding.
        return {"kind": "insufficient_data", "stage": None,
                "why": "not enough baseline data to judge"}
    if result["merged_per_hour"] >= baseline * THROUGHPUT_FRACTION:
        return None

    found = result["anomalies"] if "anomalies" in result else anomalies(result)
    opened, opened_baseline = result["opened_per_hour"], result["baseline_opened_per_hour"]
    intake_down = (
        opened_baseline
        and opened < opened_baseline * THROUGHPUT_FRACTION
        and result["baseline_opened_count"] >= MIN_COMPLETIONS
    )

    if intake_down and not found:
        return {
            "kind": "intake", "stage": None,
            "why": (
                f"fewer pull requests are arriving: {opened:.2f}/h against "
                f"{opened_baseline:.2f}/h. Nothing is stuck; there is less to merge"
            ),
        }
    if found:
        primary = dict(found[0], kind="stage")
        if intake_down:
            primary["why"] += (
                f". Arrivals are also down, at {opened:.2f}/h against "
                f"{opened_baseline:.2f}/h, so the queue is both thinner and slower"
            )
        return primary
    return {
        "kind": "unexplained", "stage": None,
        "why": (
            f"arrivals are steady at {opened:.2f}/h and no stage is backing up, "
            "so the fall is not explained by the queue"
        ),
    }


def report(result: dict) -> str:
    lines = []
    merged, baseline = result["merged_per_hour"], result["baseline_merged_per_hour"]
    change = f"{merged / baseline:.0%} of baseline" if baseline else "no baseline"
    lines.append(f"{result['repo']}  ({result['open_prs']} open)")
    lines.append(
        f"  merged {merged}/h over the last {result['window_hours']:.0f}h "
        f"against {baseline}/h over {result['baseline_hours'] / 24:.0f}d — {change}"
    )
    lines.append(
        f"  opened {result['opened_per_hour']}/h against {result['baseline_opened_per_hour']}/h"
    )
    lines.append("")
    header = f"  {'stage':<20}{'depth':>6}{'oldest':>9}{'in/h':>7}{'out/h':>7}{'dwell':>8}{'normal':>8}"
    lines.append(header)
    lines.append("  " + "-" * (len(header) - 2))
    for stage in result["stages"]:
        mark = " " if stage["owned_by_project"] else "*"
        dwell = stage["median_dwell_hours"]
        normal = stage["baseline_median_dwell_hours"]
        lines.append(
            f"  {mark}{stage['stage']:<19}{stage['depth']:>6}"
            f"{stage['oldest_waiting_hours']:>8.0f}h"
            f"{stage['entered_per_hour']:>7}{stage['left_per_hour']:>7}"
            f"{(f'{dwell:.1f}h' if dwell is not None else '-'):>8}"
            f"{(f'{normal:.1f}h' if normal is not None else '-'):>8}"
        )
    lines.append("")
    lines.append("  * waiting on the contributor, not on the project")
    lines.append("")
    if result.get("open_prs_without_a_lifecycle_label"):
        lines.append(
            f"  note: {result['open_prs_without_a_lifecycle_label']} open PR(s) carry no single "
            "lifecycle label, so they are absent from every depth above"
        )

    cause = result["cause"]
    if cause is None:
        lines.append("  throughput is normal; no stage is backing up")
    elif cause["kind"] == "stage":
        lines.append(f"  cause: {cause['stage']} — {cause['why']}")
        for other in (result.get("anomalies") or [])[1:]:
            lines.append(f"  also:  {other['stage']} — {other['why']}")
    else:
        lines.append(f"  cause: {cause['why']}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", default="TauCetiProject/TauCeti")
    parser.add_argument("--data", type=Path, help="replay a normalized offline snapshot")
    parser.add_argument("--dump-data", type=Path, help="write the fetched snapshot")
    parser.add_argument("--out", type=Path, help="write the JSON result here")
    parser.add_argument("--window", type=float, default=24.0, help="recent window, hours")
    parser.add_argument("--baseline", type=float, default=14 * 24.0, help="baseline, hours")
    parser.add_argument("--json", action="store_true", help="print JSON instead of a report")
    parser.add_argument("--as-of", type=parse_dt,
                        help="analyse as at this instant (default: the snapshot's fetched_at)")
    args = parser.parse_args(argv)

    snapshot = json.loads(args.data.read_text()) if args.data else fetch_snapshot(args.repo)
    if args.dump_data:
        args.dump_data.write_text(json.dumps(snapshot, indent=1))

    result = rounded(analyse(snapshot, args.window, args.baseline, args.as_of))

    if args.out:
        # Atomically, matching pr_stats_graphs.py: a half-written JSON file is
        # worse than a missing one, because everything downstream trusts it.
        atomic_write(args.out, json.dumps(result, indent=1))
    print(json.dumps(result, indent=1) if args.json else report(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
