# PR status mirroring

Surface where every TauCeti PR sits in the pipeline, in two places, from one
source of truth:

- **GitHub labels**: exactly one status label on each open PR, visible in the PR
  list and searchable.
- **Zulip reactions**: one bot-owned message per PR in the **Tau Ceti** channel,
  carrying emoji that track the same states at a glance.

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
| ci `running` | `awaiting-CI` | 🟡 `yellow` |
| ci not reported | `awaiting-CI` | *(no CI reaction)* |
| ci `failure` | `awaiting-author` | 🔴 `red_circle` |
| ci `success`, review `changes` | `awaiting-author` | 🟢 + ✍️ `writing` |
| ci `success`, review `approved` | `ready-to-merge` | 🟢 + ✔️ `check` |
| ci `success`, review pending, live marker | `review-in-progress` | 🟢 + 👀/▶️ |
| ci `success`, review pending, no marker | `awaiting-review` | 🟢 + 👀/▶️ |

Both review signals (the scoreboard meta and the in-progress marker) are read
only from comments by a repo-associated author (OWNER/MEMBER/COLLABORATOR), from
one comment fetch, so a fork PR author cannot forge review state. Every reconcile
reads GitHub afresh and drives the sink to the correct state, so the same command
powers the event-driven workflows and a one-shot backfill, and a transient hiccup
self-heals on the next event. The only dependencies are python3's standard library
and an authenticated `gh` CLI, nothing from PyPI.

## Labels

The five labels are mutually exclusive; [`labels.py`](labels.py) sets one and
removes any other, so exactly one is present on an open PR (none on a terminal
PR). All five are provisioned on first use, and **`labels.py` is the sole writer
of them**: the "exactly one" invariant is CI's alone to keep, and it assumes
nothing about any worker or review harness. That is deliberate: anyone can point
their own review harness at TauCeti, and CI must not depend on a particular one.

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
| **CI (build)** | running | 🟡 `yellow` |
| | passed | 🟢 `green_circle` |
| | failed | 🔴 `red_circle` |
| **Review / lifecycle** | review has begun | 👀 `eyes` |
| | running, green so far | ▶️ `play` |
| | changes requested / blocked | ✍️ `writing` |
| | all review done, all green | ✔️ `check` |
| | merged | `:merge:` |
| | closed, not merged | `:closed-pr:` |

The message is found-or-created from the PR's title *before* the fallible CI and
review reads, so a transient GitHub hiccup can never leave a PR without its
durable Zulip message. Only the bot's *own* reactions are authoritative (presence
is judged by the bot's user id), so a human reacting on a status message never
confuses reconciliation.

Three workflows drive it:

- [`zulip-pr.yml`](../../.github/workflows/zulip-pr.yml): on PR
  `opened`/`reopened`/`closed`. Creates the message and owns the merged/closed
  ending.
- [`zulip-pr-status.yml`](../../.github/workflows/zulip-pr-status.yml): on
  `workflow_run` of `pr-build` and `Review`. Refreshes the CI and review groups.
- [`zulip-healthcheck.yml`](../../.github/workflows/zulip-healthcheck.yml): a
  schedule (every 6h) that runs `check` to probe the credentials, so a broken
  key is caught even during quiet periods with no PR activity.

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

# Zulip: needs the bot credentials exported. Ascending == chronological.
export ZULIP_API_KEY=... ZULIP_EMAIL=... ZULIP_SITE=https://leanprover.zulipchat.com
for pr in $(gh pr list --repo TauCetiProject/TauCeti --state all --limit 1000 --json number --jq '.[].number' | sort -n); do
  python3 scripts/pr_status/zulip.py reconcile "$pr" --create
done
```

Re-running either is safe: it converges to current GitHub state and changes
nothing else. `pr-labels.yml` also has a `workflow_dispatch` that reconciles a
single PR's label from the Actions tab.

## Unit tests

```bash
cd scripts/pr_status
python3 -m unittest test_pr_labels test_stuck_alerts
```

`test_pr_labels` covers the derivation (`core.review_state`, `core.inprogress_from`,
`core.derive`), the label collapse (`labels.derived_label`), and the reconcile
convergence, all with the GitHub reads and label writes stubbed, so it needs no
network.
