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

from pr_stats_graphs import (  # noqa: E402
    LIFECYCLE_LABELS,
    STATE_AUTHOR_ACTION,
    fetch_snapshot,
    iso_z,
    parse_dt,
)

# Reported in pipeline order, which is also the order to read them in: a stage
# is only the bottleneck if the ones feeding it are keeping up.
STAGE_ORDER = [
    "awaiting-CI",
    "awaiting-review",
    "review-in-progress",
    "ready-to-merge",
    "ci-failed",
    "awaiting-author",
]
OWNED_BY_PROJECT = [s for s in STAGE_ORDER if s not in STATE_AUTHOR_ACTION]


def lifecycle_intervals(pr: dict, now: datetime):
    """Yield (label, entered, left) for each spell the PR spent in a stage.

    The pipeline keeps exactly one lifecycle label on a PR at a time, so
    consecutive label events bound each spell. An open PR's final spell is still
    running, and is reported with `left` as None.
    """
    events = [
        (parse_dt(e["created_at"]), e["label"])
        for e in sorted(pr.get("labeled_events") or [], key=lambda e: e["created_at"])
        if e["label"] in LIFECYCLE_LABELS
    ]
    for index, (entered, label) in enumerate(events):
        if index + 1 < len(events):
            yield label, entered, events[index + 1][0]
        elif pr["state"] == "OPEN":
            yield label, entered, None
        else:
            closed = parse_dt(pr.get("merged_at") or pr.get("closed_at"))
            yield label, entered, closed or now


def rate(count: int, hours: float) -> float:
    return count / hours if hours else 0.0


def median(values: list[float]) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[middle]
    return (ordered[middle - 1] + ordered[middle]) / 2


def analyse(snapshot: dict, window_hours: float, baseline_hours: float, now: datetime) -> dict:
    prs = snapshot["prs"]
    window_start = now - timedelta(hours=window_hours)
    baseline_start = now - timedelta(hours=baseline_hours)

    entered = defaultdict(lambda: {"window": 0, "baseline": 0})
    left = defaultdict(lambda: {"window": 0, "baseline": 0})
    dwell = defaultdict(lambda: {"window": [], "baseline": []})
    depth: defaultdict[str, int] = defaultdict(int)
    oldest: dict[str, float] = {}

    for pr in prs:
        for label, start, end in lifecycle_intervals(pr, now):
            if start >= baseline_start:
                entered[label]["baseline"] += 1
            if start >= window_start:
                entered[label]["window"] += 1

            if end is None:
                # Still in this stage: it contributes to depth and to how long
                # the stage's current occupants have been waiting, but not to
                # completed dwell times, which would bias them downwards.
                depth[label] += 1
                waiting = (now - start).total_seconds() / 3600
                oldest[label] = max(oldest.get(label, 0.0), waiting)
                continue

            hours = (end - start).total_seconds() / 3600
            if end >= baseline_start:
                left[label]["baseline"] += 1
                dwell[label]["baseline"].append(hours)
            if end >= window_start:
                left[label]["window"] += 1
                dwell[label]["window"].append(hours)

    def opened_or_merged(field: str, since: datetime) -> int:
        return sum(
            1 for pr in prs
            if pr.get(field) and parse_dt(pr[field]) >= since
        )

    stages = []
    for label in STAGE_ORDER:
        baseline_dwell = median(dwell[label]["baseline"])
        window_dwell = median(dwell[label]["window"])
        stages.append({
            "stage": label,
            "owned_by_project": label not in STATE_AUTHOR_ACTION,
            "depth": depth[label],
            "oldest_waiting_hours": round(oldest.get(label, 0.0), 1),
            "entered_per_hour": round(rate(entered[label]["window"], window_hours), 2),
            "left_per_hour": round(rate(left[label]["window"], window_hours), 2),
            "baseline_entered_per_hour": round(rate(entered[label]["baseline"], baseline_hours), 2),
            "baseline_left_per_hour": round(rate(left[label]["baseline"], baseline_hours), 2),
            "median_dwell_hours": round(window_dwell, 2) if window_dwell is not None else None,
            "baseline_median_dwell_hours": round(baseline_dwell, 2) if baseline_dwell is not None else None,
        })

    result = {
        "schema_version": 1,
        "repo": snapshot.get("repo"),
        "generated_at": iso_z(now),
        "snapshot_fetched_at": snapshot.get("fetched_at"),
        "window_hours": window_hours,
        "baseline_hours": baseline_hours,
        "opened_per_hour": round(rate(opened_or_merged("created_at", window_start), window_hours), 2),
        "baseline_opened_per_hour": round(rate(opened_or_merged("created_at", baseline_start), baseline_hours), 2),
        "merged_per_hour": round(rate(opened_or_merged("merged_at", window_start), window_hours), 2),
        "baseline_merged_per_hour": round(rate(opened_or_merged("merged_at", baseline_start), baseline_hours), 2),
        "open_prs": sum(1 for pr in prs if pr["state"] == "OPEN"),
        "stages": stages,
    }
    result["bottleneck"] = find_bottleneck(result)
    return result


def find_bottleneck(result: dict) -> dict | None:
    """The stage most responsible for the pipeline being slower than usual.

    Judged on backing up rather than on depth: a stage can be deep and perfectly
    healthy if it is draining as fast as it fills. What matters is arrivals
    outrunning departures, and occupants waiting longer than they normally do.
    """
    if result["merged_per_hour"] >= result["baseline_merged_per_hour"] * 0.75:
        return None

    scored = []
    for stage in result["stages"]:
        if not stage["owned_by_project"] or not stage["depth"]:
            continue
        arriving = stage["entered_per_hour"]
        leaving = stage["left_per_hour"]
        # How far behind the stage is falling, relative to its own normal pace.
        backlog_growth = arriving - leaving
        baseline_dwell = stage["baseline_median_dwell_hours"] or 0
        slowdown = 0.0
        if baseline_dwell and stage["oldest_waiting_hours"]:
            slowdown = stage["oldest_waiting_hours"] / baseline_dwell
        scored.append((backlog_growth > 0, slowdown, backlog_growth, stage))

    if not scored:
        return None
    scored.sort(key=lambda item: (item[0], item[1], item[2]), reverse=True)
    growing, slowdown, growth, stage = scored[0]

    if growing:
        why = (
            f"arriving at {stage['entered_per_hour']}/h and leaving at "
            f"{stage['left_per_hour']}/h, so it is filling faster than it drains"
        )
    elif slowdown > 2:
        why = (
            f"its oldest occupant has waited {stage['oldest_waiting_hours']}h against a "
            f"{stage['baseline_median_dwell_hours']}h normal dwell"
        )
    else:
        why = f"{stage['depth']} waiting, the deepest project-owned stage"
    return {"stage": stage["stage"], "why": why, "depth": stage["depth"]}


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
    bottleneck = result["bottleneck"]
    if bottleneck:
        lines.append(f"  bottleneck: {bottleneck['stage']} — {bottleneck['why']}")
    elif baseline and merged < baseline:
        lines.append("  throughput is down but no stage is backing up; likely a quiet spell in arrivals")
    else:
        lines.append("  throughput is normal; no stage is backing up")
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
    args = parser.parse_args(argv)

    snapshot = json.loads(args.data.read_text()) if args.data else fetch_snapshot(args.repo)
    if args.dump_data:
        args.dump_data.write_text(json.dumps(snapshot, indent=1))

    now = datetime.now(timezone.utc)
    result = analyse(snapshot, args.window, args.baseline, now)

    if args.out:
        args.out.write_text(json.dumps(result, indent=1))
    print(json.dumps(result, indent=1) if args.json else report(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
