# Pipeline health

`scripts/pipeline_health.py` answers "where is the pull-request pipeline slow,
and why", which merge throughput on its own cannot: throughput is one number at
the end of a queue, so a fall in it says something is wrong without saying what.

It measures each lifecycle stage separately — arrival rate, departure rate,
current depth, how long the oldest occupant has waited, and median dwell — each
against a trailing baseline, and names the cause: a stage backing up, an intake
that has thinned, both, or neither.

## Reading it

```
scripts/pipeline_health.py             # fetch and report
scripts/pipeline_health.py --json      # machine-readable
```

Three things it deliberately does not do.

**Depth is not evidence.** A stage can be very deep and perfectly healthy if it
drains as fast as it fills. The bottleneck is chosen on arrivals outrunning
departures, and on occupants waiting longer than that stage normally takes.

**A thin intake is an answer, not a shrug.** Fewer merges can mean the queue is
stuck or simply that less went into it, and those want opposite responses:
adding review capacity does nothing about a week when nobody opened anything. So
arrival rates are compared against baseline too, and a fall in them is reported
as the cause. When both are true, both are said.

**A building queue is reported before throughput falls.** A stage taking in more
than it lets out is what a fall in throughput looks like before it arrives, so
`anomalies` is populated whether or not merges have dropped yet. `cause` is
separate, and answers only "why is throughput down" when it is.

**It will admit to not knowing.** If arrivals are steady and no stage is backing
up, the fall is reported as unexplained rather than pinned on whichever stage
happened to be deepest. A baseline with too few merges reports insufficient data
rather than health.

**`ci-failed` and `awaiting-author` are never blamed.** Those wait on the
contributor rather than on the project, and treating a backlog there as
something to fix would point effort at exactly the wrong place. They are
reported, marked with `*`, and excluded from the bottleneck.

Depths come from the labels a PR currently carries, not from the last event in
its timeline, so a PR whose label was removed is not counted in a stage it has
left. Open PRs carrying no single lifecycle label are counted separately and
reported, rather than silently omitted.

## Where the data comes from

The same normalized snapshot the statistics charts use, so this adds no new API
surface. Fetching it walks every pull request's label timeline, which is
thousands of requests and takes tens of minutes, so:

- **the Pages workflow** fetches once, writes the charts, and derives
  `pipeline-health.json` from the same snapshot;
- **anything else** should read the published
  `https://taucetiproject.github.io/TauCeti/static/pipeline-health.json`
  rather than repeat the walk.

To work offline, dump a snapshot once and replay it:

```
scripts/pr_stats_graphs.py --dump-data snap.json --out-dir /tmp/charts
scripts/pipeline_health.py --data snap.json
```

A replay is measured as at the snapshot's `fetched_at`, not as at now, so an old
snapshot gives the answer it would have given when it was taken. `--as-of`
overrides that.

The baseline window is disjoint from the recent one, and both are clamped to the
date the lifecycle labels landed, so a wide baseline is not diluted by time in
which no event could have been recorded.

That is also how the tests run, so they need no network.
