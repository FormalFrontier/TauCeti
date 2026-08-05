# PR status mirroring

Surface where every TauCeti PR sits in the pipeline, in two places, from one
source of truth:

- **GitHub labels**: exactly one status label on each open PR, visible in the PR
  list and searchable.
- **Zulip reactions**: one bot-owned message per PR in the **Tau Ceti** channel,
  carrying emoji that track the same states at a glance.
- **A comment on the PR**, for the one state that needs to reach an author who
  has stopped looking: a merge conflict.

[`core.py`](core.py) is that source of truth. It derives a PR's status from
GitHub (PR state, the `build` commit status, the canonical
`<!--tauceti-scoreboard-->` comment's meta JSON, and the review engine's
`<!--tauceti-review-in-progress-->` marker) and returns a neutral
`{lifecycle, ci, review, review_inprogress}`. It writes nothing. The two *sinks*
import it and only differ in how they render that one status, so labels and
reactions can never disagree:

| `core.derive` | `labels.py` (one label) | `zulip.py` (two reaction groups) |
| --- | --- | --- |
| lifecycle `merged` / `closed` | *(no label)* | `:merge:` / `:closed-pr:` |
| conflicting | `merge-conflict` | ⚠️ `warning` |
| ci `running` | `awaiting-CI` | 🟡 `yellow` |
| ci not reported | `awaiting-CI` | 🟡 `yellow` |
| ci `failure` | `awaiting-author` | 🔴 `red_circle` |
| ci `success`, review `changes` | `awaiting-author` | 🟢 + ✍️ `writing` |
| ci `success`, review `approved` | `ready-to-merge` | 🟢 + ✔️ `check` |
| ci `success`, review pending, live marker | `review-in-progress` | 🟢 + 👀 |
| ci `success`, review pending, no marker | `awaiting-review` | 🟢 |

Both review signals (the scoreboard meta and the in-progress marker) are read
only from comments by a repo-associated author (OWNER/MEMBER/COLLABORATOR), from
one comment fetch, so a fork PR author cannot forge review state. Every reconcile
reads GitHub afresh and drives the sink to the correct state, so the same command
powers the event-driven workflows and a one-shot backfill, and a transient hiccup
self-heals on the next event. The only dependencies are python3's standard library
and an authenticated `gh` CLI, nothing from PyPI.

## Labels

The six labels are mutually exclusive; [`labels.py`](labels.py) sets one and
removes any other, so exactly one is present on an open PR (none on a terminal
PR). All six are provisioned on first use, and **`labels.py` is the sole writer
of them**: the "exactly one" invariant is CI's alone to keep, and it assumes
nothing about any worker or review harness. That is deliberate: anyone can point
their own review harness at TauCeti, and CI must not depend on a particular one.
The conflict sweep is a *caller* of `labels.reconcile`, not a second writer.

`merge-conflict` outranks the other five, because it is the one state in which
nothing downstream can make progress: a green build and an approving review on
the current head still cannot merge. It is also the only state derived from a
tri-state — GitHub computes mergeability lazily, and `conflicting is None` means
"not computed", never "no conflict", so an uncomputed PR keeps whatever label it
had rather than being painted either way.

`review-in-progress` is derived, like the other four, from a signal CI reads
rather than from anyone writing the label. The signal is the review engine's
in-flight marker (`<!--tauceti-review-in-progress-->`, carrying a `head` and an
`expires_at`), treated as an **optional, documented** contract that any review
harness MAY post: an unexpired, head-exact marker while the PR is otherwise
`awaiting-review` shows `review-in-progress`. A harness that posts no marker just
leaves the PR at `awaiting-review` during review, which is never wrong; and the
marker's TTL means a crashed review self-heals, since the hourly `sweep` job
clears the label once the marker expires even if no other event fires.

The review verdict itself comes from the scoreboard's durable per-rubric `states`
map, not the latest round's `runs`: a reply/partial round re-runs only some
rubrics, so `runs` alone can show a green latest round while another rubric still
blocks. This mirrors the worker's `ledger_blocking` and the signal CI's merge
close reads (see [`core.review_state`](core.py)), and falls back to `runs` only
for a legacy scoreboard without a `states` map.

[`pr-labels.yml`](../../.github/workflows/pr-labels.yml) drives it. A first
`resolve` job resolves the PR number once; the `label` job then keys its
`concurrency` on that number, so every trigger for one PR shares a group and two
events can never interleave a label add/remove. It runs under a GitHub App token
scoped to this repo, and, like the roadmap and Zulip workflows, never checks out
or runs PR head code. Triggers:

- `pull_request_target` (opened/reopened/synchronize/closed): new commit or the
  terminal strip.
- `workflow_run` of `pr-build` (completed): the build verdict. (Not `requested`:
  a late `requested` for an old head could force `awaiting-CI` onto a moved PR,
  and a new commit already paints `awaiting-CI` via `synchronize`.)
- `issue_comment` carrying the scoreboard or in-progress marker.
- `schedule` (hourly): the `sweep` backstop that clears an expired
  `review-in-progress`.
- `workflow_dispatch`: manual re-sync of one PR.

## Zulip reactions

[`zulip.py`](zulip.py) finds-or-creates the PR's message in the **PRs** topic and
reconciles two independent, mutually-exclusive reaction groups from `core.derive`:

| Group | State | Emoji |
| --- | --- | --- |
| **CI (build)** | waiting / running | 🟡 `yellow` |
| | passed | 🟢 `green_circle` |
| | failed | 🔴 `red_circle` |
| **Review / lifecycle** | conflicts with main | ⚠️ `warning` |
| | review in progress | 👀 `eyes` |
| | waiting for review | *(none)* |
| | changes requested / blocked | ✍️ `writing` |
| | all review done, all green | ✔️ `check` |
| | merged | `:merge:` |
| | closed, not merged | `:closed-pr:` |

Each message includes the PR's author and the area from every `roadmap/...`
label (with `unlabelled` distinct from the deliberate `roadmap/none`). A later
label change edits the existing message in place, so a roadmap label added after
the PR opens is still shown. The message is found-or-created from the PR's
metadata *before* the fallible CI and review reads, so a transient GitHub hiccup
can never leave a PR without its durable Zulip message. Only the bot's *own*
reactions are authoritative (presence is judged by the bot's user id), so a
human reacting on a status message never confuses reconciliation.

Three event-driven workflows drive it:

- [`zulip-pr.yml`](../../.github/workflows/zulip-pr.yml): on PR
  `opened`/`reopened`/`closed` and label changes. Creates the message, keeps its
  roadmap metadata current, and owns the merged/closed ending. The automatic
  status-label transitions also make review reactions refresh promptly; on an
  open PR they can self-heal a message missed by a transient opening failure,
  while label churn on a closed PR can never create a late post.
- [`zulip-pr-status.yml`](../../.github/workflows/zulip-pr-status.yml): on
  `workflow_run` of `pr-build` and `Review`. Refreshes the CI and review groups.
- [`zulip-healthcheck.yml`](../../.github/workflows/zulip-healthcheck.yml): a
  schedule (every 6h) that runs `check` to probe the credentials, so a broken
  key is caught even during quiet periods with no PR activity.

## Merge conflicts

A PR becomes conflicted because **main moved**, not because its author did
anything. That makes it the one transition no other workflow here can see: every
other trigger is scoped to the PR (`pull_request_target`, a `pr-build` / `Review`
`workflow_run`, an `issue_comment`), and main moving fires none of them. Before
[`conflicts.py`](conflicts.py) existed, a PR could pick up a conflict and
*nothing anywhere said so* — no label, no reaction, no comment, no alert.
`stuck_alerts.py` deliberately skips a conflicting PR (it is not being wrongly
withheld by the merge path) and `housekeeping.py` only retires PRs that are
blocking under review, so a conflicted-but-approved PR was reaped by nothing
either. It rotted silently.

[`conflict-sweep.yml`](../../.github/workflows/conflict-sweep.yml) runs the sweep
on every push to main — the exact moment conflicts are created — and hourly as a
backstop. One GraphQL query reads mergeability for every open PR at once, so a
sweep costs one request plus a handful for the PRs that actually changed.

The **comment** is the part that matters, because it is the only one of the three
sinks that generates a GitHub notification, and therefore the only one that
reaches an author whose session has ended. There is exactly one per conflict
*episode*, carrying a hidden `<!--tauceti-conflict:v1 {"onset": …}-->` marker:

- while the conflict persists the comment is left **byte-identical** — this is a
  notice, not a nag;
- when the PR merges cleanly again the comment is **edited** to a ✅ form
  recording `resolved`;
- a *second* conflict posts a **new** comment, since editing the buried ✅ one
  would notify nobody.

Two things guard against the worst failure an autonomous notifier can have, which
is posting comments it should not. **Every write is re-confirmed**: the sweep reads
the whole queue in one query and then works through it, so before posting or
resolving anything it re-reads that one PR and requires the head OID, the base OID,
and the mergeability to all still match what it saw. A push landing mid-sweep makes
it skip the PR rather than comment about a state the PR has already left. And the
marker comments are read with a trust rule of their own — `conflicts.ours`, not
`core.trusted_comments`: a GitHub App's installation bot comments as
`author_association: CONTRIBUTOR`, which the latter excludes, so reading markers
through it would mean the sweep never recognised a comment it had just written and
posted another on every run, forever. A fork PR author is a `User` with no repo
association and so still cannot forge a marker to silence their own notice.

A PR carrying a hold label (`keep`/`hold`/`wip`/`human`/`do-not-close`/`blocked`)
still gets the label and the reaction — the queue view should be honest — but no
comment, because it is parked on purpose. The label goes on the moment the conflict
is *seen*, so if such a PR is later unparked while still conflicting, the episode is
dated from that `labeled` event rather than from the sweep that finally comments —
otherwise a conflict of days would be reported as one of minutes. A conflict that
both starts and clears while the PR is parked never gets a comment at all, and is
recorded by the label's `labeled`/`unlabeled` pair alone: a durable record that
costs no extra write and notifies nobody. `report` reads those back as
*unannounced* episodes, so withholding the notice does not quietly shorten the
measurement — see below.

The label and the ⚠️ are re-asserted on **every** sweep for a PR that is currently
conflicting. During an episode nothing else fires for that PR — that is this
module's whole premise — so a sink lost to a failed write would otherwise stay lost
for exactly the window it exists to cover. Both sinks are convergent, so a sweep
that finds them already right costs reads and no writes; once the conflict clears,
the PR's own events (a push runs `pr-build`, which refreshes Zulip) take over.

GitHub computes `mergeable` lazily, so the first read after main moves answers
UNKNOWN and schedules the merge in the background. The sweep re-reads the unknowns
a few times; anything still unknown is **left exactly as it is**, neither
announced nor cleared, and picked up an hour later. "We could not compute it" is
not evidence either way. A PR stuck at UNKNOWN *permanently* is a different fault
— GitHub has stopped recomputing it, usually a head diverged from its branch tip —
and `stuck_alerts.py`'s `diverged-head` detector escalates that, so a PR this
sweep can never see is surfaced rather than dropped.

### Measuring it

The marker's `onset`/`resolved` pair is what makes conflict-to-resolution
*measurable*, which it previously was not: GitHub reports only the current value
of `mergeable` and its timeline records nothing when a PR starts conflicting.

```bash
python3 scripts/pr_status/conflicts.py report            # median, tail, per author
python3 scripts/pr_status/conflicts.py report --days 14 --json
```

`report` reads **closed and merged PRs as well as open ones**, which is not a
detail: a conflict that was resolved and then merged is exactly the case that must
not be dropped, or the median would improve every time the queue got healthier. A
PR closed while still conflicting is reported as *censored* — an outcome, not a
resolution time — and kept out of the median rather than counted either way.

It also reads each PR's `merge-conflict` **label timeline**, for the same reason:
an episode that came and went while the PR was parked has no comment to be found
by, and dropping those would drop precisely the conflicts nobody was chasing. They
count towards the headline median, which is queue-wide because that is what the 24h
target names, and are then broken out as *parked* with their own median — the one
population that contains no author latency at all, since nobody was told.

The first sweep dates every *already*-conflicting PR from the moment it ran, so
its first day of output understates those ages. History from before the markers
existed has to be reconstructed from git — replaying each PR head against every
`main` commit with `git merge-tree` — which is its own tool and not part of this
package.

## Stuck-automation alerts (Tau Ceti > "Stuck PRs")

[`stuck_alerts.py`](stuck_alerts.py), driven by
[`stuck-alerts.yml`](../../.github/workflows/stuck-alerts.yml) hourly, posts to a
second topic (**Stuck PRs**) whenever Tau Ceti's own automation wedges and cannot
recover on its own. It reuses `core`'s GitHub-truth helpers and `zulip`'s Zulip
client (pointed at the topic via `ZULIP_TOPIC`) and is idempotent the same way:
one bot message per active alert, tagged with a hidden `<!--stuck:v1 <key>-->`
marker, edited to a ✅ checkmark when the situation clears and never re-posted
while it persists.

This is an **emergency channel, not a help queue.** Every alert means a piece of
infrastructure needs fixing so the wedge cannot recur, not that a human should
hand-hold one PR. It fires on: a red, stale last-known-good bump PR; a mathlib pin
that has stopped advancing; an in-scope, fully-green PR the merge path never
merged; an open `Review stuck: PR #…` issue; a scheduled workflow that is disabled
or overdue; `main` gone red; and a long-open mathlib-incompatibility issue. It
**deliberately does not** alert on normal backlog (a PR awaiting its first review
verdict, changes-requested nobody addressed, open roadmap issues); the module
docstring lists the full catalogue and the reasoning.

Run `python3 scripts/pr_status/stuck_alerts.py --dry-run` (with `gh` authenticated)
to print the alerts it would post without touching Zulip. Its run goes red only on
a persistent Zulip config break, exactly like the healthcheck.

## One-time setup

1. **Create a dedicated Zulip bot** (Zulip → Settings → Bots → Add a new bot,
   type *Generic*). Subscribe it to the **Tau Ceti** channel: a bot can only
   post and react in channels it belongs to.
2. **Add repository secrets** on `TauCetiProject/TauCeti`:
   - `ZULIP_API_KEY`: the bot's API key
   - `ZULIP_EMAIL`: the bot's email (e.g. `tauceti-pr-bot@leanprover.zulipchat.com`)

   The site is hard-coded to `https://leanprover.zulipchat.com` in the workflows.

   > **Set the key without a trailing newline.** A newline (or stray
   > whitespace) rides into the Basic-auth header and Zulip rejects the key as
   > `Malformed API key` (a 401). Use `--body`, which does not append one:
   >
   > ```bash
   > gh secret set ZULIP_API_KEY --repo TauCetiProject/TauCeti --body "$KEY"
   > ```
   >
   > Avoid `echo "$KEY" | gh secret set ...` (echo adds a newline). The script
   > also `.strip()`s both creds defensively, but set them cleanly anyway.

The labels need no secret: `pr-labels.yml` uses the same GitHub App
(`APP_ID` / `APP_PRIVATE_KEY`) already configured for the roadmap and merge
workflows, scoped to this repo, and provisions the five labels on first use.

## Failure modes (Zulip)

The Zulip integration is quiet about cosmetic problems and loud about real ones,
because the two are easy to confuse from the outside:

- A **transient** hiccup (one Zulip 5xx, a network blip, a PR with no message
  yet) is cosmetic and self-heals on the next reconcile. The script logs it and
  exits 0, so the workflow run stays green.
- A **configuration** break (missing/empty creds, a bad API key (401), a
  forbidden bot (403), or the bot not subscribed to the channel) breaks *every*
  PR and will not fix itself. The script logs it, emits a GitHub Actions
  `::error::` annotation, and exits non-zero, so the workflow run goes **red**.

When a run is red, re-set `ZULIP_API_KEY` per the gotcha above, then confirm:

```bash
export ZULIP_API_KEY=... ZULIP_EMAIL=... ZULIP_SITE=https://leanprover.zulipchat.com
python3 scripts/pr_status/zulip.py check   # exits 0 and prints OK when healthy
```

## Backfill (run locally)

To seed labels and/or Zulip messages for PRs that predate this integration, run
the reconcilers over the open PRs with `gh` authenticated:

```bash
# Labels: needs only an authenticated gh with issues:write.
for pr in $(gh pr list --repo TauCetiProject/TauCeti --state open --json number --jq '.[].number'); do
  python3 scripts/pr_status/labels.py reconcile "$pr"
done

# Zulip: needs the status bot credentials exported. This paginates the complete
# PR history in one low-request stream and edits existing posts in place,
# including posts whose URL predates the FormalFrontier -> TauCetiProject transfer.
export ZULIP_API_KEY=... ZULIP_EMAIL=... ZULIP_SITE=https://leanprover.zulipchat.com
gh api --paginate \
  'repos/TauCetiProject/TauCeti/pulls?state=all&sort=created&direction=asc&per_page=100' \
  --jq '.[] | {
    number,
    state,
    merged: (.merged_at != null),
    head: .head.sha,
    title,
    author: .user.login,
    roadmaps: [.labels[].name | select(startswith("roadmap/"))]
  }' | python3 scripts/pr_status/zulip.py backfill --dry-run --strict

# After reviewing the dry-run summary, omit --dry-run to apply it.
```

Re-running either is safe: it converges to current GitHub state and changes
nothing else. The `Zulip PR backfill` workflow runs the same full-history post
update with the repository's status-bot secrets, so old posts can be migrated
without copying credentials locally. It defaults to a dry run, continues past
individual failures and reports them together, retries transient Zulip failures,
and intentionally does not create missing messages. `pr-labels.yml` also has a
`workflow_dispatch` that reconciles a single PR's label from the Actions tab.

## Unit tests

```bash
cd scripts/pr_status
python3 -m unittest test_pr_labels test_zulip test_stuck_alerts
```

`test_pr_labels` covers the derivation (`core.review_state`, `core.inprogress_from`,
`core.derive`), metadata plumbing, the label collapse (`labels.derived_label`),
and reconcile convergence. `test_zulip` covers review reactions, PR post
rendering, legacy-message rewriting, batch continuation, dry runs, and rate-limit
retry. All GitHub and Zulip reads and writes are stubbed, so these need no
network.
