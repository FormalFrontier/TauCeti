# Lean CI performance gate

## Outcome

Tau Ceti rejects accidental elaboration catastrophes before they reach `main`
without making merges wait for the external radar service. The required build
has a per-Lean-process wall-clock ceiling, and the parallel `perf` status checks
each added or modified Lean module. It uses retired hardware instructions where
the runner exposes them and same-runner CPU time on GitHub's hosted VMs, whose
virtual CPUs do not expose that performance counter.

This is a CI gate, not a source linter. In particular, it does not try to guess
which uses of `decide`, kernel reduction, or metaprogramming are expensive.

## Policy

- Every Lean compiler process in the required build, the performance job, and
  the advisory heartbeat pass has 300 seconds of wall time. On expiry the
  watchdog sends `SIGTERM`, waits 30 seconds, then sends `SIGKILL` to the Lean
  process group. The command fails with exit code 124 (or 137 when escalation
  to `SIGKILL` is required).
- A modified or renamed Lean file fails the instruction gate only when its head
  measurement is both at least 1.5 times its immutable-base measurement and at
  least 100 billion instructions larger.
- A new Lean file fails at 500 billion instructions.
- On a runner without a retired-instruction counter, the corresponding CPU-time
  fallback fails a modified file at both 1.5 times base and +30 CPU-seconds, and
  a new file at 150 CPU-seconds. Base and head run on the same VM. The 300-second
  module wall limit remains the primary hard stop in either mode.
- Deleted files pass and are reported. Missing measurements for the selected
  metric, failed elaboration, truncated file lists, or setup errors fail
  closed. An unavailable instruction counter selects the CPU fallback only
  after its own preflight succeeds.
- Mathlib's `countHeartbeats` profile remains advisory. It is useful diagnostic
  information, but it is not a substitute for the instruction or wall-time
  gates because kernel reduction can consume CPU without consuming heartbeats.

## Security model

The performance workflow uses `pull_request_target` so its definition and
performance tooling come from the trusted `github.workflow_sha` (the base
commit for untrusted PR events). It checks out the candidate without credentials
and overlays only regular files under `TauCeti/` (and `TauCeti.lean`) onto a
trusted checkout. Lake pins are overlaid only after the
trusted `check-bump.sh` validates the same forward-only transition accepted by
the required build. Candidate lakefiles and scripts are never run.

Every command that may elaborate candidate Lean code runs inside `landrun`:

- no network permission;
- no GitHub token or cache endpoint in the environment allowlist;
- read-only access to `/usr`, `/etc`, elan, and the overlaid checkout;
- write access only to that checkout's `.lake` directory; and
- the existing `/dev/shm`, network, and out-of-tree-write self-tests must pass
  before candidate code runs.

The networked setup fetches Mathlib oleans and Tau Ceti's public, main-built
artifact cache using only trusted base configuration. Cache endpoints and
network access are not passed into `landrun`. The cache may prepare dependency
cones, but it is explicitly disabled after the selected module output is
invalidated, so the measured build must invoke Lean for that module.

The trusted host invokes `perf stat` or GNU `time` *around* `landrun`.
GitHub-hosted runners set `perf_event_paranoid=4` and expose no virtual hardware
instruction event, so the workflow deliberately does not lower that global
protection or introduce a privileged monitor. It selects the unprivileged
instruction counter only when a preflight proves it works; otherwise it uses
unprivileged process CPU time. Raw measurement output is written under
`RUNNER_TEMP`, which is not mounted into the sandbox. Candidate code therefore
cannot edit its base/head measurements or verdict. After base measurement is
complete, its `.lake` artifact tree is hardlinked into the head workspace to
avoid a multi-minute copy; candidate writes can affect those retired cache
inodes, but base is never executed or read as evidence again. Trusted scripts,
config, manifests, and raw results are not in that writable tree. Status posting
and Markdown rendering happen after the sandbox exits.

The watchdog itself runs inside `landrun`. A trusted host step prepares a
toolchain-shaped directory whose `bin/lean` is the watchdog, whose
`bin/lean-real` points at the pinned elan compiler, and whose remaining files
point at that same pinned toolchain. The directory is mounted read-only. This
shape is necessary because Lake uses `LEAN` to discover a toolchain root and
then reconstructs `<root>/bin/lean`; merely naming an arbitrary wrapper in
`LEAN` would silently lose the wrapper after discovery. The workflow does not
pass the watchdog's test-only timeout environment variables into the sandbox,
so candidate code cannot raise or disable the production limits.

## Expected happy-path cost and rollout checks

The watchdog starts one small shell/`timeout` wrapper per Lean compiler process. Its
target budget on ordinary required builds is the larger of 20 seconds or 5%
at p90. The performance workflow runs in parallel with `pr-build`; for PRs with
at most five changed Lean files its target is a median duration below four
minutes and p90 below six minutes. Since it is parallel, the merge-readiness
target is a median added delay of zero and p90 no more than 60 seconds. Host
measurement-wrapper overhead should remain below 3% in paired measurements.

Parallelism removes the extra job from a PR's critical path only while a hosted
runner is available. It does not make the extra runner-minutes free: under
repository or organization-wide saturation, one performance job per active PR
can lengthen the queue for unrelated builds. Rollout measurements must therefore
separate queue delay from job execution time and record total runner-minutes as
well as the per-PR completion delta. If the latency target passes only when queue
time is excluded, the gate is slowing CI in the happy case and needs capacity or
a cheaper measurement design before it becomes required.

The implementation uses GNU `timeout` through a small shell wrapper (not a
Python interpreter per module). A local 200-process startup microbenchmark
measured about 4.3 ms median and 5.6 ms p90 added cost per invocation. Even if
all 1,895 current Tau Ceti modules rebuild, that is roughly eight CPU-seconds of wrapper
startup, parallelized with the build; cache-hit PRs pay it only for modules Lake
actually invokes. This is encouraging but is not a substitute for the paired
CI measurements below, which include runner scheduling and filesystem effects.

Before making `perf` a required repository status:

1. Run the branch-defined workflow against the historical E8 regression. It
   must terminate the offending module at 300 seconds and report failure.
2. Run it against the representative E6 work. It must pass both budgets.
3. Sample at least 20 ordinary open PRs, including new, modified, renamed, and
   pin-bump cases. Record workflow duration and the difference between `build`
   and `perf` completion times.
4. Compare required builds with and without the watchdog on cache-hit and
   cache-miss cases. Check the p90 budget above.
5. After a human reviews and lands the infrastructure PR, add `perf` to the
   repository's required statuses. Do not require it before the base workflow
   exists, because that would leave every PR waiting for a status no workflow
   can post.

During the first week, inspect every timeout or module-cost failure manually.
If noise requires tuning, change thresholds in a separately reviewed
infrastructure PR; do not add source-level bypasses or per-file exceptions.

## Pre-merge validation (2026-08-12)

- The [historical E8 regression](https://github.com/TauCetiProject/TauCeti/actions/runs/31561889305)
  passed landrun's confinement checks, entered the prepared read-only wrapper,
  and stopped `E8.lean` at 300 seconds with exit code 124. The trusted report
  failed closed and posted a terminal failing `perf` status. The head phase
  took 303 seconds; the full job took 8 minutes 3 seconds including setup and
  cache preparation.
- The [representative E6 addition](https://github.com/TauCetiProject/TauCeti/actions/runs/31561994227)
  passed at 59.6 CPU-seconds. Its active job time was 5 minutes 28 seconds.
- An [ordinary modified file](https://github.com/TauCetiProject/TauCeti/actions/runs/31561995756)
  passed at 5.0 seconds on base and 4.9 seconds on head. Its active job time was
  3 minutes 40 seconds, versus 6 minutes 7 seconds for that commit's required
  build, so spare-runner parallel execution would add no merge-readiness delay.

The two happy-path validation jobs waited about 6.5 and 7.2 minutes for runners
during a heavily saturated repository interval. Those waits are excluded from
the active durations above but are evidence for the fleet-capacity caveat, not
evidence that it can be ignored. The 20-PR queue and completion-time sample is
still required before rollout is considered validated.
