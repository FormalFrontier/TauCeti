#!/usr/bin/env python3
"""Assign each PR the roadmap it advances, as a `roadmap/<Area>` label.

The label is derived, not asked for: a submitter already has to name the roadmap
their new mathematics advances (the scope rubric in TauCetiReview requires it),
so we read that citation back out of the PR body rather than burden them with a
second, structured field.

## The classifier (see `classify`)

A PR gets exactly one label, decided in this order:

1. `roadmap/none` -- the diff touches an infrastructure path (anything outside
   `TauCeti/`, the root `TauCeti.lean`, and the two ordinary Lake pins). This also
   covers the review bot's narrowly validated first-known-bad lakefile exception:
   either way it is infrastructure, not roadmap work.
2. `roadmap/<Area>` -- the body cites exactly one canonical roadmap, e.g.
   `TauCetiRoadmap/OneParameterSemigroups/README.md` or `ContourIntegration/README.md`.
   `<Area>` is the roadmap directory name, the same source of truth
   `check_roadmap_areas.py` uses in the roadmap repo.
3. `roadmap/none` -- no single citation, but the title is a refactor/fix/chore/...
   (or a Mathlib bump). Reworking already-merged material needs no roadmap claim,
   so absence of a citation is correct here, not a defect.
4. `roadmap/Unknown` -- a new-mathematics PR (a `feat:` touching only `TauCeti/`)
   that cites no parseable roadmap file. The live workflow leaves a one-time nudge
   asking the author to cite the roadmap file, exactly as the scope rubric wants.

The area set is read at runtime from a checkout of the roadmap repo, so a roadmap
added there becomes labelable with no change here; the label itself is created on
first use (`ensure_label`).

## Usage

    # classify one PR and print the label (no writes):
    roadmap_label.py --pr 781 --repo TauCetiProject/TauCeti --roadmap-dir roadmap
    # ... and apply it (create the label if missing, drop any stale roadmap/* label),
    # leaving a nudge if it lands in roadmap/Unknown:
    roadmap_label.py --pr 781 --repo ... --roadmap-dir roadmap --apply --nudge
    # backfill every PR (never nudges):
    roadmap_label.py --backfill --repo ... --roadmap-dir roadmap --apply

`--apply`/`--nudge` shell out to `gh`, which must be authenticated (GH_TOKEN).
`classify` and the parsing helpers are pure and are what the tests exercise.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
import time

# --- label namespace -------------------------------------------------------

NONE_LABEL = "roadmap/none"
UNKNOWN_LABEL = "roadmap/Unknown"


def area_label(area: str) -> str:
    return f"roadmap/{area}"


# Colours are cosmetic; kept uniform so the namespace reads as one group.
AREA_COLOR = "1d76db"      # blue: a resolved roadmap
NONE_COLOR = "ededed"      # grey: not roadmap work
UNKNOWN_COLOR = "fbca04"   # yellow: needs a citation

# --- the CI-allowed path set ----------------------------------------------

# A PR whose files all match this is one an AI author may land without a human
# override: `TauCeti/`, the root aggregator, and the two bump-guarded Lake pins.
# The build workflow has one author-aware extension to this set: a PR opened by the
# trusted review bot may pin Mathlib's lakefile rev to an exactly validated SHA. It
# remains an infrastructure PR and therefore still belongs under roadmap/none here.
_ALLOWED_PATH = re.compile(r"^(?:TauCeti/|TauCeti\.lean$|lake-manifest\.json$|lean-toolchain$)")

# Titles that, by convention, rework existing material rather than add new
# mathematics; per the scope rubric these need no roadmap claim.
_NONROADMAP_TITLE = re.compile(
    r"^(?:refactor|fix|chore|style|test|perf|docs?|ci|build|revert|harden)(?:[(!:/]| )",
    re.IGNORECASE,
)


def is_infra(files: list[str]) -> bool:
    """True if any changed path is one CI would not let an AI PR touch alone.

    An empty file list is treated as infra (fail closed, as the scope guard does):
    we could not see a diff, so we do not claim a roadmap for it.
    """
    if not files:
        return True
    return any(not _ALLOWED_PATH.match(f) for f in files)


def parse_cited_areas(body: str, areas: set[str]) -> set[str]:
    """Roadmap areas cited in the PR body, restricted to canonical ones.

    Recognizes the forms authors actually use: a `TauCetiRoadmap/<Area>` path, and
    a bare `<Area>/README.md` or `<Area>/Suggested.lean`. `<Area>` must be an
    existing roadmap directory, so a typo or an unrelated path is ignored rather
    than minting a bogus label.
    """
    if not body:
        return set()
    found: set[str] = set()
    for m in re.finditer(r"TauCetiRoadmap/([A-Za-z0-9]+)", body):
        if m.group(1) in areas:
            found.add(m.group(1))
    for m in re.finditer(r"\b([A-Za-z0-9]+)/(?:README\.md|Suggested\.lean)", body):
        if m.group(1) in areas:
            found.add(m.group(1))
    return found


def classify(title: str, body: str, files: list[str], areas: set[str]) -> str:
    """Return the single roadmap label for a PR. Pure; see module docstring."""
    if is_infra(files):
        return NONE_LABEL
    cited = parse_cited_areas(body, areas)
    if len(cited) == 1:
        return area_label(next(iter(cited)))
    # Zero citations, or several (no single roadmap to name): fall through.
    if _NONROADMAP_TITLE.match(title or ""):
        return NONE_LABEL
    return UNKNOWN_LABEL


# --- roadmap area discovery ------------------------------------------------


def canonical_areas(roadmap_dir: pathlib.Path) -> set[str]:
    """Roadmap directory names (those containing a README.md) under a checkout.

    Accepts either the roadmap repo root (areas live under its inner
    `TauCetiRoadmap/` package dir) or the package dir itself.
    """
    inner = roadmap_dir / "TauCetiRoadmap"
    base = inner if inner.is_dir() else roadmap_dir
    return {p.name for p in base.iterdir() if p.is_dir() and (p / "README.md").is_file()}


# --- gh plumbing (only reached in --apply/--nudge/--pr/--backfill IO paths) --


def _gh(args: list[str], retries: int = 3) -> str:
    """Run `gh`, retrying transient failures (API 5xx, secondary rate limits).

    Every call site is idempotent (label add/remove, `label create --force`, and
    comments guarded by a marker), so a retry after a partial failure is safe.
    """
    last = ""
    for attempt in range(retries):
        r = subprocess.run(
            ["gh", *args], text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        )
        if r.returncode == 0:
            return r.stdout or ""
        last = r.stderr or ""
        if attempt < retries - 1:
            time.sleep(2 * (attempt + 1))
    raise RuntimeError(f"gh {' '.join(args)} failed after {retries} tries: {last}")


def ensure_label(repo: str, name: str, color: str, desc: str) -> None:
    """Create the label if missing (idempotent; `--force` heals colour/desc)."""
    _gh([
        "label", "create", name, "--repo", repo,
        "--color", color, "--description", desc, "--force",
    ])


def _label_meta(name: str, areas: set[str]) -> tuple[str, str]:
    if name == NONE_LABEL:
        return NONE_COLOR, "PR advances no roadmap (infra, refactor, or a Mathlib bump)"
    if name == UNKNOWN_LABEL:
        return UNKNOWN_COLOR, "New mathematics PR with no parseable roadmap citation"
    return AREA_COLOR, "PR advances the {} roadmap".format(name[len("roadmap/"):])


NUDGE_MARKER = "<!--roadmap-label:nudge-->"
NUDGE_BODY = (
    NUDGE_MARKER + "\n"
    "This PR adds new mathematics but I could not find the roadmap it advances "
    "in its description, so I have labelled it `roadmap/Unknown`.\n\n"
    "Per the [scope rubric](https://github.com/TauCetiProject/TauCetiReview/blob/main/rubrics/scope.md), "
    "new material should identify the roadmap file and node it advances. Please add "
    "a reference to the roadmap file, for example "
    "`TauCetiRoadmap/OneParameterSemigroups/README.md`, and the label will update "
    "automatically. If this PR only reworks already-merged material, no roadmap is "
    "needed and you can ignore this."
)


def apply_label(repo: str, pr: int, target: str, areas: set[str]) -> None:
    """Set the PR's roadmap/* label to `target`, removing any stale ones."""
    color, desc = _label_meta(target, areas)
    ensure_label(repo, target, color, desc)
    current = json.loads(_gh([
        "pr", "view", str(pr), "--repo", repo, "--json", "labels",
    ]))["labels"]
    have = {l["name"] for l in current}
    stale = [n for n in have if n.startswith("roadmap/") and n != target]
    edits: list[str] = []
    if target not in have:
        edits += ["--add-label", target]
    for s in stale:
        edits += ["--remove-label", s]
    if edits:  # nothing to do when the PR already carries exactly this label
        _gh(["pr", "edit", str(pr), "--repo", repo, *edits])


def _already_nudged(repo: str, pr: int) -> bool:
    comments = json.loads(_gh([
        "pr", "view", str(pr), "--repo", repo, "--json", "comments",
    ]))["comments"]
    return any(NUDGE_MARKER in (c.get("body") or "") for c in comments)


def nudge(repo: str, pr: int) -> None:
    """Post the citation nudge once (idempotent via a hidden marker)."""
    if _already_nudged(repo, pr):
        return
    _gh(["pr", "comment", str(pr), "--repo", repo, "--body", NUDGE_BODY])


def _pr_fields(repo: str, pr: int) -> tuple[str, str, list[str]]:
    d = json.loads(_gh([
        "pr", "view", str(pr), "--repo", repo, "--json", "title,body,files",
    ]))
    return d.get("title") or "", d.get("body") or "", [f["path"] for f in d.get("files") or []]


# --- CLI -------------------------------------------------------------------


def _run_one(args, areas) -> int:
    title, body, files = _pr_fields(args.repo, args.pr)
    label = classify(title, body, files, areas)
    print(f"#{args.pr}\t{label}\t{title}")
    if args.apply:
        apply_label(args.repo, args.pr, label, areas)
        if args.nudge and label == UNKNOWN_LABEL:
            nudge(args.repo, args.pr)
    return 0


def _run_backfill(args, areas) -> int:
    prs = json.loads(_gh([
        "pr", "list", "--repo", args.repo, "--state", "all",
        "--limit", str(args.limit), "--json", "number,title,body,files,state",
    ]))
    from collections import Counter
    tally: Counter[str] = Counter()
    plan = []
    for p in prs:
        files = [f["path"] for f in p.get("files") or []]
        label = classify(p.get("title") or "", p.get("body") or "", files, areas)
        tally[label] += 1
        plan.append((p["number"], label))
        print(f"#{p['number']}\t{p['state']}\t{label}\t{p.get('title','')}")

    failed: list[int] = []
    if args.apply:
        # A per-PR failure must not abandon the rest of the backfill; collect and
        # retry once at the end (transient API errors are already retried in _gh).
        for num, label in plan:
            try:
                apply_label(args.repo, num, label, areas)  # never nudges
            except Exception as e:  # noqa: BLE001 -- keep going, report at the end
                print(f"  ! #{num}: {e}", file=sys.stderr)
                failed.append(num)
        for num in list(failed):
            label = dict(plan)[num]
            try:
                apply_label(args.repo, num, label, areas)
                failed.remove(num)
            except Exception as e:  # noqa: BLE001
                print(f"  ! #{num} (retry): {e}", file=sys.stderr)

    print("\n=== summary ===", file=sys.stderr)
    for name, n in sorted(tally.items(), key=lambda kv: -kv[1]):
        print(f"  {name:24} {n}", file=sys.stderr)
    if failed:
        print(f"  UNAPPLIED (needs another run): {failed}", file=sys.stderr)
        return 1
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Assign roadmap labels to PRs.")
    ap.add_argument("--repo", default="TauCetiProject/TauCeti")
    ap.add_argument("--roadmap-dir", required=True,
                    help="path to a TauCetiRoadmap checkout (for the canonical area set)")
    ap.add_argument("--pr", type=int, help="classify a single PR")
    ap.add_argument("--backfill", action="store_true", help="classify every PR")
    ap.add_argument("--limit", type=int, default=5000, help="max PRs for --backfill")
    ap.add_argument("--apply", action="store_true", help="write the label to the PR(s)")
    ap.add_argument("--nudge", action="store_true",
                    help="with --pr --apply: comment once when the label is roadmap/Unknown")
    a = ap.parse_args(argv)

    areas = canonical_areas(pathlib.Path(a.roadmap_dir))
    if not areas:
        print(f"no roadmap areas found under {a.roadmap_dir}", file=sys.stderr)
        return 2
    if a.backfill:
        return _run_backfill(a, areas)
    if a.pr is not None:
        return _run_one(a, areas)
    ap.error("one of --pr or --backfill is required")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
