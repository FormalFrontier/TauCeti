# Working in Tau Ceti

This is the AI-owned code repo of Tau Ceti. Read `README.md` for what the project is and how
the three repos fit together; this file only adds the contract for agents working here.

## Before you write code

**Read the roadmap first.** The roadmaps live in the separate
[TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap) repo. The roadmap gates
*new* mathematics: only add a new mathematical declaration (definition, theorem, instance,
notation) or file when it advances a specific roadmap target, or supplies a prerequisite that a
specific target needs. If a human asks you to build something new that is not on the roadmap,
say so and ask them to add it to the roadmap first, rather than building it here.

Improving code that already exists is **always in scope** and needs no roadmap entry:
refactoring, simplifying proofs, fixing or modestly generalising an existing lemma (without
expanding the project's mathematical scope), relocating a misplaced declaration, adopting a
cleaner idiom, and documenting existing code are all welcome at any time. The roadmap conditions
what new mathematics gets *added*, not whether already-merged code may be made better.

## The rules of the repo

- `main` is always green. CI builds against pinned Mathlib and enforces: no `sorry`, no
  axioms beyond `propext`, `Classical.choice`, `Quot.sound` (so no `native_decide`), and the
  Mathlib linter set (style, file length, no `maxHeartbeats` overrides). Do not try to disable
  these.
- One topic per PR. Ship a prerequisite refactor as its own PR.
- `TauCeti/` is the only place code goes. `scripts/`, `.github/`, and the lakefile
  (`lakefile.toml`/`lakefile.lean`) are human-owned. The two Lake *pins* —
  `lake-manifest.json` and `lean-toolchain` — are an exception: a **forward-only** bump of
  them (Mathlib moving forward on the branch the lakefile nominates, with the toolchain moving
  monotonically forward) is machine-validated by the `bump-guard` check and is welcome, but
  never edit the lakefile or move a pin backward. The sole automated exception is an
  incompatibility PR opened by `tauceti-review-bot[bot]`: it may pin Mathlib's lakefile `rev`
  to the same immutable first-known-bad SHA recorded in the manifest, and the following compatible
  bot bump may restore that line to `master`. The trusted bump guard validates those exact one-line
  transitions before either can build or merge.
- **Never delete a PR's human-owned changes to get it past the build gate.** When a PR
  *intentionally* touches `scripts/`, `.github/`, or the lakefile (for example, a PR that adds
  a new CI check), those changes are the deliverable, not an obstacle. The gate routes such a
  PR to a human on purpose; the correct response is to wait for that human review and merge,
  never to strip the human-owned files so the PR looks auto-mergeable — that throws away the
  work the PR exists to do. This binds automated fix/review agents too: if a PR carries
  human-owned changes, leave it alone (skip it) rather than "fixing" it toward auto-merge.
- **Do not `--admin`-merge AI-authored PRs.** Landing a PR is the review pipeline's job: it
  merges only once every rubric is green (and, for `TauCeti/`-only diffs, CI is green). Using an
  admin override to bypass that gate — even when the reviews have not been run — defeats the
  project's quality control. If the pipeline is not producing verdicts, run the review
  (`tauceti-review`) or leave the PR for a human; never force it through.

## How review works

Open a PR. After CI passes, AI review agents judge it against the rubrics in
[TauCetiReview](https://github.com/TauCetiProject/TauCetiReview) (correctness, reuse, API,
naming, placement, proofs, and more) and post `approve` / `request_changes` / `block`
verdicts. Address their findings and push; re-review runs automatically on new commits, and a
human can comment `/review` to re-trigger.

If two findings contradict — one requires X while another requires not-X, or a later round
reverses a change an earlier finding required — do not silently satisfy one and let the other
re-fire. Contest one of the threads, link the conflicting one, and quote its wording (rubric
and round). Explain why both cannot hold. Show the contradiction; do not just assert one.

When every rubric approves on the current commit and the PR changes only `TauCeti/` (with CI
green), it **merges automatically**. A PR that *also* changes `lake-manifest.json` and/or
`lean-toolchain` can auto-merge too, but only once the `bump-guard` check confirms it is a
forward-only bump and the sandboxed build passes against the new pins. The exact review-bot
first-known-bad lakefile pin described above can auto-merge under the same checks. A PR that
touches any other human-owned path (`scripts/`, `.github/`, or any other lakefile change) always
needs a human review. The
review pipeline is sandboxed so it can run on untrusted PRs; see
[`SECURITY.md`](https://github.com/TauCetiProject/TauCetiReview/blob/main/SECURITY.md) in
TauCetiReview.
