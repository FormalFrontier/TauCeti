#!/usr/bin/env python3
"""Evaluate module-cost budgets and render the required perf report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


MODIFIED_MIN_DELTA = 100_000_000_000
MODIFIED_RATIO = 1.5
NEW_FILE_LIMIT = 500_000_000_000
CPU_MODIFIED_MIN_DELTA = 30.0
CPU_NEW_FILE_LIMIT = 150.0
MARKER = "<!-- lean-performance-comment -->"


def fmt(value: int | float | None, metric: str) -> str:
    if value is None:
        return "—"
    if metric == "instructions":
        return f"{value / 1_000_000_000:,.1f}B"
    return f"{value:,.1f}s"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--head", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--metric", choices=("instructions", "cpu"), required=True)
    parser.add_argument("--run-url", default="")
    args = parser.parse_args()

    entries = json.loads(args.manifest.read_text())
    base = {row["slug"]: row for row in json.loads(args.base.read_text())}
    head = {row["slug"]: row for row in json.loads(args.head.read_text())}
    rows: list[tuple[str, str, int | float | None, int | float | None, str]] = []
    failed = False
    min_delta = MODIFIED_MIN_DELTA if args.metric == "instructions" else CPU_MODIFIED_MIN_DELTA
    new_limit = NEW_FILE_LIMIT if args.metric == "instructions" else CPU_NEW_FILE_LIMIT

    for entry in entries:
        kind, slug = entry["kind"], entry["slug"]
        if kind == "removed":
            rows.append((entry["base_path"], "removed", None, None, "pass"))
            continue
        head_row = head.get(slug)
        head_value = head_row.get("value") if head_row else None
        if (not isinstance(head_value, (int, float)) or head_row.get("status") != "ok"
                or head_row.get("metric") != args.metric):
            rows.append((entry["head_path"], kind, None, None, "measurement failed"))
            failed = True
            continue
        if kind == "added":
            verdict = "pass" if head_value < new_limit else f"fail (≥ {fmt(new_limit, args.metric)})"
            failed |= head_value >= new_limit
            rows.append((entry["head_path"], kind, None, head_value, verdict))
            continue
        base_row = base.get(slug)
        base_value = base_row.get("value") if base_row else None
        if (not isinstance(base_value, (int, float)) or base_row.get("status") != "ok"
                or base_row.get("metric") != args.metric):
            rows.append((entry["head_path"], kind, None, head_value, "base measurement failed"))
            failed = True
            continue
        delta = head_value - base_value
        regression = delta >= min_delta and head_value >= MODIFIED_RATIO * base_value
        floor = "+100B" if args.metric == "instructions" else "+30s CPU"
        verdict = f"fail (≥1.5× and {floor})" if regression else "pass"
        failed |= regression
        rows.append((entry["head_path"], kind, base_value, head_value, verdict))

    out = [MARKER + "\n", "## Lean performance gate\n\n"]
    if args.metric == "instructions":
        out.append(
            "Required retired-instruction check. Modified files fail only when the head is at least "
            "1.5× base **and** adds at least 100B instructions; new files fail at 500B. "
        )
    else:
        out.append(
            "Required CPU-time fallback (this runner exposes no retired-instruction counter). "
            "Modified files fail only when the head is at least 1.5× base **and** adds at least "
            "30 CPU-seconds; new files fail at 150 CPU-seconds. "
        )
    out.append("Every Lean process also has a 300s wall-clock limit.\n\n")
    if rows:
        out.extend(("| File | Change | Base | Head | Verdict |\n", "|---|---|---:|---:|---|\n"))
        for path, kind, old, new, verdict in rows:
            out.append(
                f"| `{path}` | {kind} | {fmt(old, args.metric)} | "
                f"{fmt(new, args.metric)} | {verdict} |\n"
            )
    else:
        out.append("_No added or modified `TauCeti/` Lean files._\n")
    out.append("\n")
    if args.run_url:
        out.append(f"<sub>[measurement run]({args.run_url}) · re-run with `/profile`</sub>\n")
    args.output.write_text("".join(out))
    print("performance gate:", "FAIL" if failed else "PASS")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
