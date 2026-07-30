#!/usr/bin/env python3
"""Generate a self-contained "lines of code by date" SVG from git history.

Pure stdlib: no third-party dependencies, so CI needs no `pip install`.

For each day on which a matching commit landed, counts the total lines present
in the files matching the given pathspecs at that day's latest commit — exactly
what `wc -l` would report on a checkout. The whole series is reconstructed from
git each run, so there is no state file to keep up to date. Counting the lines
that exist (rather than summing diffs) needs no special handling for merges,
renames, or binary files.

Styled to sit on the dark navy Tau Ceti site (see web/static_files/style.css).
"""

import subprocess, sys, argparse, datetime as dt, html, math

# Palette mirrors style.css so the chart matches the site.
BG      = "#101936"   # panel over the navy gradient
PANEL   = "#1b2547"
GRID    = "rgba(255,255,255,0.08)"
AXIS    = "rgba(255,255,255,0.18)"
TEXT    = "#eef2fb"
MUTED   = "#9aa6c9"


def git(repo, *args):
    return subprocess.run(["git", "-C", repo, *args],
                          capture_output=True, text=True).stdout


def count_lines(repo, commit, pathspecs):
    """Total lines in the matching files at `commit` (binary files excluded)."""
    out = git(repo, "grep", "-I", "-c", "^", commit, "--", *pathspecs)
    return sum(int(line.rsplit(":", 1)[1]) for line in out.splitlines())


def series(repo, pathspecs, ref):
    # The last commit to land on each day that touched the files, keyed by
    # commit date (%cd): the date the code actually entered the repo, which is
    # the faithful x-axis for a lines-over-time chart and is monotonic under
    # --reverse, so the chart never runs backwards. Author date (%ad) is freely
    # rewritable by rebase and squash, which is what made the days arrive out of
    # order before. Keying on commit date also keeps the newest point at HEAD,
    # so the "as of" label reflects the current repo. The sort is insurance
    # against history rewrites that leave commit dates out of order; dates are
    # ISO YYYY-MM-DD, so lexicographic order is chronological.
    #
    # --first-parent walks the mainline only, so the chart tracks the size of
    # the branch itself. Without it, a commit on a feature branch is sampled on
    # its own (earlier) date, and count_lines there sees the whole branch tree,
    # so a large branch shows up as a spike on the day it was written that
    # vanishes the next day and only truly lands when the branch merges.
    day_commit = {}
    for line in git(repo, "log", "--first-parent", "--reverse", "--date=short",
                    "--format=%cd %H", ref, "--", *pathspecs).splitlines():
        date, commit = line.split()
        day_commit[date] = commit
    return [(date, count_lines(repo, commit, pathspecs))
            for date, commit in sorted(day_commit.items())]


def nice_ceil(x):
    """Round up to a 1/2/2.5/5 * 10^k value for a tidy axis top."""
    if x <= 0:
        return 1
    mag = 10 ** math.floor(math.log10(x))
    for m in (1, 2, 2.5, 5, 10):
        if x <= m * mag:
            return int(m * mag)
    return int(10 * mag)


def render(data, title, accent, out):
    W, H = 900, 460
    L, R, T, B = 72, 28, 60, 52      # margins
    pw, ph = W - L - R, H - T - B

    d0 = dt.date.fromisoformat(data[0][0])
    d1 = dt.date.fromisoformat(data[-1][0])
    span = max((d1 - d0).days, 1)
    ymax = nice_ceil(max(v for _, v in data))

    def X(d): return L + (dt.date.fromisoformat(d) - d0).days / span * pw
    def Y(v): return T + ph - v / ymax * ph

    pts = [(X(d), Y(v)) for d, v in data]
    line = " ".join(f"{x:.1f},{y:.1f}" for x, y in pts)
    area = f"{L},{T+ph} " + line + f" {L+pw},{T+ph}"

    yticks = []
    for i in range(6):
        v = ymax * i // 5
        y = Y(v)
        yticks.append(f'<line class="grid" x1="{L}" y1="{y:.1f}" x2="{L+pw}" y2="{y:.1f}"/>')
        yticks.append(f'<text class="ytick" x="{L-12}" y="{y+4:.1f}">{v:,}</text>')

    # x ticks: walk left to right, label only when >= 78px past the last label
    # (so runs of consecutive days don't collide); always keep first and last.
    xticks, last_x = [], -1e9
    for i, (d, _) in enumerate(data):
        x = X(d)
        forced = i == 0 or i == len(data) - 1
        if forced or x - last_x >= 78:
            if i == len(data) - 1 and xticks and x - last_x < 78:
                xticks.pop()        # drop a label that would crowd the final one
            dd = dt.date.fromisoformat(d)
            lab = f"{dd:%b} {dd.day}"   # avoid the GNU-only %-d
            xticks.append(f'<text class="xtick" x="{x:.1f}" y="{T+ph+24}">{lab}</text>')
            last_x = x

    dots = "".join(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="3"/>' for x, y in pts)
    latest = data[-1][1]
    grad = "g" + accent.lstrip("#")

    svg = f'''<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}"
     font-family="ui-sans-serif,system-ui,-apple-system,'Segoe UI',Roboto,sans-serif" role="img"
     aria-label="{html.escape(title)}: {latest:,} lines as of {data[-1][0]}">
  <defs>
    <linearGradient id="{grad}" x1="0" y1="0" x2="0" y2="1">
      <stop offset="0" stop-color="{accent}" stop-opacity="0.28"/>
      <stop offset="1" stop-color="{accent}" stop-opacity="0"/>
    </linearGradient>
  </defs>
  <style>
    .grid{{stroke:{GRID};stroke-width:1}}
    .axis{{stroke:{AXIS};stroke-width:1}}
    .ytick{{fill:{MUTED};font-size:13px;text-anchor:end}}
    .xtick{{fill:{MUTED};font-size:13px;text-anchor:middle}}
    .title{{fill:{TEXT};font-size:19px;font-weight:600}}
    .sub{{fill:{MUTED};font-size:13px}}
    .line{{fill:none;stroke:{accent};stroke-width:2.5;stroke-linejoin:round;stroke-linecap:round}}
    circle{{fill:{accent}}}
  </style>
  <rect x="0.5" y="0.5" width="{W-1}" height="{H-1}" rx="12" fill="{BG}" stroke="{PANEL}"/>
  <text class="title" x="{L}" y="30">{html.escape(title)}</text>
  <text class="sub" x="{L}" y="48">{latest:,} lines as of {data[-1][0]}</text>
  {''.join(yticks)}
  <line class="axis" x1="{L}" y1="{T}" x2="{L}" y2="{T+ph}"/>
  <line class="axis" x1="{L}" y1="{T+ph}" x2="{L+pw}" y2="{T+ph}"/>
  <polygon points="{area}" fill="url(#{grad})"/>
  <polyline class="line" points="{line}"/>
  {dots}
  {''.join(xticks)}
</svg>
'''
    with open(out, "w") as f:
        f.write(svg)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--ref", default="HEAD")
    ap.add_argument("--title", required=True)
    ap.add_argument("--accent", default="#ff9d4d")
    ap.add_argument("--out", required=True)
    ap.add_argument("pathspecs", nargs="+")
    a = ap.parse_args()
    data = series(a.repo, a.pathspecs, a.ref)
    if not data:
        sys.exit("no commits matched pathspecs")
    render(data, a.title, a.accent, a.out)
    print(f"wrote {a.out}: {len(data)} points, latest {data[-1][1]:,}")
