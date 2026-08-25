# Pipeline health

`scripts/pipeline_health.py` answers "where is the pull-request pipeline slow,
and why", which merge throughput on its own cannot: throughput is one number at
the end of a queue, so a fall in it says something is wrong without saying what.

It measures each lifecycle stage separately — arrival rate, departure rate,
current depth, how long the oldest occupant has waited, and median dwell — each
against a trailing baseline, and names the stage most responsible.

## Reading it

```
scripts/pipeline_health.py             # fetch and report
scripts/pipeline_health.py --json      # machine-readable
```

Two things it deliberately does not do.

**Depth is not evidence.** A stage can be very deep and perfectly healthy if it
drains as fast as it fills. The bottleneck is chosen on arrivals outrunning
departures, and on occupants waiting longer than that stage normally takes.

**`ci-failed` and `awaiting-author` are never blamed.** Those wait on the
contributor rather than on the project, and treating a backlog there as
something to fix would point effort at exactly the wrong place. They are
reported, marked with `*`, and excluded from the bottleneck.

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

That is also how the tests run, so they need no network.
