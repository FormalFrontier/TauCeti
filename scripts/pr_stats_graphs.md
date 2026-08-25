# Pull-request statistics graphs

`pr_stats_graphs.py` regenerates the five pull-request statistics assets intended for
the Tau Ceti Statistics page:

```sh
python3 scripts/pr_stats_graphs.py \
  --repo TauCetiProject/TauCeti \
  --out-dir web/static_files
```

It requires an authenticated `gh` CLI. In GitHub Actions, set `GH_TOKEN` to
`${{ github.token }}` and grant `pull-requests: read` plus `issues: read`.

## Definitions

- **Total time open** is snapshot time minus PR creation time for every open PR.
- **Awaiting author** covers both states that put the ball in the author's court,
  `ci-failed` and `awaiting-author`, and starts when the PR entered that pair. Swapping
  one for the other continues the same clock; going back through `awaiting-CI` starts a
  new one.
- **In review** starts when the current review cycle began; the pipeline's swap to
  `review-in-progress`, and any later restoration of `awaiting-review`, remain part of
  that same clock.
- **Review cycle N** means the PR has entered the review states (`awaiting-review` or
  `review-in-progress`) from an author or CI state at least N times. This must come from
  label events: scoreboard comments are edited in place and counting comments undercounts
  later rounds. Counting label applications instead would overcount, because the pipeline
  swaps `awaiting-review` for `review-in-progress` and reconciliation can restore it while
  one round is still being judged. The chart states the earliest date on which a cycle is
  observed, since PRs predating the review-state labels cannot be reconstructed from those
  transitions.
- **One review scoreboard** in the contributor history is one canonical
  `<!--tauceti-scoreboard-->` comment on a pull request of this repository, attributed to
  the GitHub login that posted it. Canonical means the comment carries the review engine's
  `<!--tauceti-meta:v1 ...-->` block, declares kind `scoreboard`, and names that same PR,
  so a comment on an ordinary issue, a quoted marker, or another PR's pasted scoreboard is
  not counted, and neither are the scoreboards from the project's first week, posted before
  the engine started stamping that block; `pr-stats.json` records how many marker comments
  were rejected and why.
  This is a count of posted scoreboards, not reconstructed review rounds; scoreboards
  edited in place remain one comment. Attribution accepts only comments whose posting
  login also authors a merged PR in the fetched snapshot. This excludes arbitrary external
  commenters without requiring the read-only Actions token to enumerate collaborators; a
  contributor who has authored a merged PR is inside this statistics trust boundary.
- Seven-day metrics use complete UTC calendar days. Merge latency is PR creation to
  merge time among PRs merged in that trailing window. Cumulative contributor histories
  include events through the snapshot time, including the current partial UTC day.

## Reproducible and offline runs

Save the normalized source snapshot while fetching:

```sh
python3 scripts/pr_stats_graphs.py \
  --repo TauCetiProject/TauCeti \
  --out-dir /tmp/pr-stats \
  --dump-data /tmp/pr-stats-source.json
```

Replay it without GitHub access:

```sh
python3 scripts/pr_stats_graphs.py \
  --data /tmp/pr-stats-source.json \
  --out-dir /tmp/pr-stats-replay
```

`--as-of` overrides the snapshot clock for deterministic fixtures. The default chart
limits can be adjusted with `--history-days`, `--contributor-limit`, and
`--max-review-cycles`.

## Scaling

GitHub pagination is explicit at both levels. PR metadata is fetched separately from
label history because GitHub can silently truncate a timeline nested inside the outer
PR connection—even when it reports no next page. Timelines are therefore queried one
at a time through authoritative direct `pullRequest(number:)` connections; batching
those direct connections can also lose events. Any timeline with more than 100 label
events is paginated separately. Each direct response also refreshes that PR's current
state and labels, avoiding skew between the outer metadata scan and the timeline used
for its state clock. PRs closed before the lifecycle-label workflow landed on
2026-07-22 have no such events and skip the timeline query. The current repository uses
about 1,000 of GitHub's 5,000-point hourly GraphQL budget per run. Excessive missing
state transitions stop generation rather than publishing a mislabelled clock. Issue
comments and their v1 metadata are filtered and parsed by `gh` before reaching Python,
so full scoreboard bodies do not accumulate in memory.

All six outputs are rendered in a staging directory and promoted only after every
chart and the JSON payload succeeds. A failed scheduled fetch therefore keeps the
previous coherent asset set.

Contributor charts plot up to 24 contributors and one aggregate `Other` series.
Only those bounded series are expanded by day. `pr-stats.json` still records the exact
all-time total for every contributor, so increasing the project from tens to thousands
of contributors does not create a thousand-line SVG or a days-times-contributors
in-memory matrix.

## Tests

The tests require no Python packages; when the `jq` executable is available they also
exercise the exact compact scoreboard filter used with `gh`:

```sh
python3 scripts/test_pr_stats_graphs.py
```

They cover direct timeline pagination, fail-closed state clocks, all-or-nothing
rendering, cycle reach beyond six, review-label churn inside one cycle, the real
scoreboard jq program, the requested queue panel order, SVG/XML validity, and a
synthetic 2,500-contributor history.
