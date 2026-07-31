#!/usr/bin/env python3
"""Generate a stacked "lines of Lean per roadmap, over time" SVG.

Unlike scripts/loc_graph.py, which counts the lines present in the tree straight
from git, this chart needs to know *which roadmap* each line belongs to — and that
attribution lives in the PR labels (`roadmap/<Area>`), not in git. So the series is
built from merged new-mathematics pull requests: each PR contributes its net diff
(additions minus deletions) to its roadmap's running total on the day it merged,
and the bands are the cumulative totals over time.

That makes this a churn-based measure (a line rewritten by a later PR is counted in
both), not a `wc -l` of the tree; it answers "how much labelled work has landed per
roadmap", which is the question the labels make answerable. Infrastructure and
unresolved `roadmap/Unknown` PRs are excluded, as are maintenance PRs recognized
from their conventional-commit title. The latter is deliberately independent of
`roadmap/none`, so adding roadmap attribution to a refactor does not change the
chart's meaning.

Data comes from `gh` by default (needs auth: GH_TOKEN with pull-requests:read), or
from a `--data` JSON file (the output of
`gh pr list --state merged --json number,title,labels,mergedAt,additions,deletions`) for
offline rendering and tests. Pure stdlib otherwise, matching loc_graph.py so CI needs
no pip install. Styled for the navy Tau Ceti site (see web/static_files/style.css).
"""

import argparse
import datetime as dt
import html
import json
import math
import re
import subprocess
import sys

# Palette mirrors style.css so the panel matches the site.
BG    = "#101936"
PANEL = "#1b2547"
GRID  = "rgba(255,255,255,0.08)"
AXIS  = "rgba(255,255,255,0.18)"
TEXT  = "#eef2fb"
MUTED = "#9aa6c9"

# A categorical palette chosen to stay distinct on the navy background. Assigned to
# roadmaps in stack order (largest band first), so the mapping is stable across runs.
PALETTE = [
    "#5eead4", "#ff9d4d", "#60a5fa", "#fb7185", "#c084fc", "#4ade80", "#fde047",
    "#22d3ee", "#f472b6", "#a3e635", "#818cf8", "#fb923c", "#38bdf8", "#f87171",
    "#2dd4bf", "#e879f9",
]

AREA_PREFIX = "roadmap/"
EXCLUDE = {"roadmap/none", "roadmap/Unknown"}
MAINTENANCE_TITLE = re.compile(
    r"^(?:refactor|fix|chore|style|test|perf|docs?|ci|build|revert|harden)(?:[(!:/]| )",
    re.IGNORECASE,
)


def fetch_gh(repo: str) -> list[dict]:
    out = subprocess.run(
        ["gh", "pr", "list", "--repo", repo, "--state", "merged", "--limit", "2000",
         "--json", "number,title,labels,mergedAt,additions,deletions"],
        check=True, text=True, stdout=subprocess.PIPE).stdout
    return json.loads(out)


def roadmap_of(pr: dict) -> str | None:
    if MAINTENANCE_TITLE.match(pr.get("title") or ""):
        return None
    labs = [l["name"] for l in pr.get("labels") or []
            if l["name"].startswith(AREA_PREFIX) and l["name"] not in EXCLUDE]
    return labs[0] if len(labs) == 1 else None


def build_series(prs: list[dict]):
    """Return (dates, roadmaps_in_stack_order, {roadmap: [cumulative per date]}, totals).

    dates are the sorted days on which any counted PR merged; each roadmap's list is
    its cumulative net lines at end of that day.
    """
    by_day_area: dict[str, dict[str, int]] = {}
    totals: dict[str, int] = {}
    for pr in prs:
        area = roadmap_of(pr)
        if area is None or not pr.get("mergedAt"):
            continue
        day = pr["mergedAt"][:10]
        net = pr["additions"] - pr["deletions"]
        by_day_area.setdefault(day, {}).setdefault(area, 0)
        by_day_area[day][area] += net
        totals[area] = totals.get(area, 0) + net

    dates = sorted(by_day_area)
    # Largest final total at the bottom of the stack (drawn first).
    order = sorted(totals, key=lambda a: -totals[a])
    cum = {a: 0 for a in order}
    series = {a: [] for a in order}
    for day in dates:
        for a in order:
            cum[a] += by_day_area[day].get(a, 0)
            if cum[a] < 0:
                raise ValueError(f"{a} has a negative cumulative line count on {day}")
            series[a].append(cum[a])
    return dates, order, series, totals


def nice_ceil(x):
    if x <= 0:
        return 1
    mag = 10 ** math.floor(math.log10(x))
    for m in (1, 2, 2.5, 5, 10):
        if x <= m * mag:
            return int(m * mag)
    return int(10 * mag)


def short(area: str) -> str:
    return area[len(AREA_PREFIX):]


def render(dates, order, series, totals, title, out):
    W, H = 1140, 520
    L, T, B = 72, 62, 52
    R = 330                          # right reserve for the legend column
    pw, ph = W - L - R, H - T - B

    d0 = dt.date.fromisoformat(dates[0])
    d1 = dt.date.fromisoformat(dates[-1])
    span = max((d1 - d0).days, 1)
    stack_top = [sum(series[a][i] for a in order) for i in range(len(dates))]
    ymax = nice_ceil(max(stack_top))

    def X(d): return L + (dt.date.fromisoformat(d) - d0).days / span * pw
    def Y(v): return T + ph - v / ymax * ph

    color = {a: PALETTE[i % len(PALETTE)] for i, a in enumerate(order)}

    # Stacked bands: walk the running baseline upward, one filled polygon per roadmap.
    bands = []
    baseline = [0.0] * len(dates)
    xs = [X(d) for d in dates]
    for a in order:
        top = [baseline[i] + series[a][i] for i in range(len(dates))]
        up = " ".join(f"{xs[i]:.1f},{Y(top[i]):.1f}" for i in range(len(dates)))
        down = " ".join(f"{xs[i]:.1f},{Y(baseline[i]):.1f}" for i in range(len(dates) - 1, -1, -1))
        bands.append(f'<polygon points="{up} {down}" fill="{color[a]}" fill-opacity="0.82" '
                     f'stroke="{color[a]}" stroke-width="0.6"/>')
        baseline = top

    yticks = []
    for i in range(6):
        v = ymax * i // 5
        y = Y(v)
        yticks.append(f'<line class="grid" x1="{L}" y1="{y:.1f}" x2="{L+pw}" y2="{y:.1f}"/>')
        yticks.append(f'<text class="ytick" x="{L-12}" y="{y+4:.1f}">{v:,}</text>')

    xticks, last_x = [], -1e9
    for i, d in enumerate(dates):
        x = xs[i]
        forced = i == 0 or i == len(dates) - 1
        if forced or x - last_x >= 90:
            if i == len(dates) - 1 and xticks and x - last_x < 90:
                xticks.pop()
            dd = dt.date.fromisoformat(d)
            xticks.append(f'<text class="xtick" x="{x:.1f}" y="{T+ph+24}">{dd:%b} {dd.day}</text>')
            last_x = x

    # Legend: swatch + roadmap + final cumulative, biggest first (stack order).
    lx = L + pw + 26
    val_x = W - 24                   # values right-aligned inside the panel margin
    ly = T + 4
    legend = [f'<text class="legendhead" x="{lx}" y="{ly-8}">roadmap — net lines</text>']
    for a in order:
        legend.append(f'<rect x="{lx}" y="{ly}" width="13" height="13" rx="3" fill="{color[a]}"/>')
        legend.append(f'<text class="legend" x="{lx+20}" y="{ly+11}">{html.escape(short(a))}</text>')
        legend.append(f'<text class="legendval" x="{val_x}" y="{ly+11}">{totals[a]:,}</text>')
        ly += 22

    grand = sum(totals.values())
    svg = f'''<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}"
     font-family="ui-sans-serif,system-ui,-apple-system,'Segoe UI',Roboto,sans-serif" role="img"
     aria-label="{html.escape(title)}: {grand:,} net lines across {len(order)} roadmaps as of {dates[-1]}">
  <style>
    .grid{{stroke:{GRID};stroke-width:1}}
    .axis{{stroke:{AXIS};stroke-width:1}}
    .ytick{{fill:{MUTED};font-size:13px;text-anchor:end}}
    .xtick{{fill:{MUTED};font-size:13px;text-anchor:middle}}
    .title{{fill:{TEXT};font-size:19px;font-weight:600}}
    .sub{{fill:{MUTED};font-size:13px}}
    .legendhead{{fill:{MUTED};font-size:12px;font-weight:600}}
    .legend{{fill:{TEXT};font-size:12.5px}}
    .legendval{{fill:{MUTED};font-size:12.5px;text-anchor:end;font-variant-numeric:tabular-nums}}
  </style>
  <rect x="0.5" y="0.5" width="{W-1}" height="{H-1}" rx="12" fill="{BG}" stroke="{PANEL}"/>
  <text class="title" x="{L}" y="30">{html.escape(title)}</text>
  <text class="sub" x="{L}" y="48">{grand:,} net lines across {len(order)} roadmaps as of {dates[-1]}</text>
  {''.join(yticks)}
  {''.join(bands)}
  <line class="axis" x1="{L}" y1="{T}" x2="{L}" y2="{T+ph}"/>
  <line class="axis" x1="{L}" y1="{T+ph}" x2="{L+pw}" y2="{T+ph}"/>
  {''.join(xticks)}
  {''.join(legend)}
</svg>
'''
    with open(out, "w") as f:
        f.write(svg)
    return grand


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default="TauCetiProject/TauCeti")
    ap.add_argument("--data", help="JSON file of merged PRs (offline); else query gh")
    ap.add_argument("--title", default="Tau Ceti — lines of Lean per roadmap")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    prs = json.load(open(a.data)) if a.data else fetch_gh(a.repo)
    dates, order, series, totals = build_series(prs)
    if not dates:
        sys.exit("no labelled merged PRs found")
    grand = render(dates, order, series, totals, a.title, a.out)
    print(f"wrote {a.out}: {len(order)} roadmaps, {len(dates)} days, {grand:,} net lines")
