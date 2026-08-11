#!/usr/bin/env python3
"""Assign each PR's declared roadmap association as a `roadmap/<Area>` label.

Every PR should carry one standalone ``Roadmap: <Area>`` or ``Roadmap: none``
line. This is attribution, not scope authorization: new mathematics must still
cite the exact roadmap target that it advances, while a refactor may associate
itself with the roadmap that chiefly motivates the cleanup.

## The classifier (see `classify`)

A PR gets exactly one label, decided in this order:

1. `roadmap/none` -- the diff touches an infrastructure path (anything outside
   `TauCeti/`, the root `TauCeti.lean`, and the two ordinary Lake pins).
2. `roadmap/none` -- the diff is a pin-only dependency bump.
3. The one valid explicit ``Roadmap:`` declaration.
4. One validated canonical ``focus`` in a ``tauceti-target:v1`` marker.
5. One canonical roadmap-file citation, for compatibility with older PR bodies.
6. `roadmap/Unknown` -- attribution is absent, invalid, or conflicting.

Evidence from steps 3--5 must agree. Area names are read at runtime from active
and completed roadmaps, and labels are created on first use (`ensure_label`).
File paths and conventional-commit titles are deliberately not used as roadmap
evidence.

## Usage

    # classify one PR and print the label (no writes):
    roadmap_label.py --pr 781 --repo TauCetiProject/TauCeti --roadmap-dir roadmap
    # ... and apply it (create the label if missing, drop any stale roadmap/* label),
    # leaving a nudge if it lands in roadmap/Unknown:
    roadmap_label.py --pr 781 --repo ... --roadmap-dir roadmap --apply --nudge
    # inspect every PR (never nudges):
    roadmap_label.py --backfill --repo ... --roadmap-dir roadmap
    # changing an existing roadmap label is deliberately opt-in:
    roadmap_label.py --backfill --repo ... --roadmap-dir roadmap \
        --apply --allow-relabel

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
_ALLOWED_PATH = re.compile(r"^(?:TauCeti/|TauCeti\.lean$|lake-manifest\.json$|lean-toolchain$)")

_PINS = {"lake-manifest.json", "lean-toolchain"}
_TARGET_MARKER = re.compile(r"<!--tauceti-target:v1 (\{[^}]*\})-->")


def is_infra(files: list[str]) -> bool:
    """True if any changed path is one CI would not let an AI PR touch alone.

    An empty file list is treated as infra (fail closed, as the scope guard does):
    we could not see a diff, so we do not claim a roadmap for it.
    """
    if not files:
        return True
    return any(not _ALLOWED_PATH.match(f) for f in files)


def is_pin_only(files: list[str]) -> bool:
    """True exactly when a nonempty diff changes only the two validated pins."""
    return bool(files) and set(files) <= _PINS


def _body_lines_outside_quotes_and_fences(body: str):
    """Yield body lines that are not inside Markdown fences or blockquotes."""
    fence = None
    for line in (body or "").splitlines():
        stripped = line.lstrip()
        marker = stripped[:3]
        if marker in {"```", "~~~"}:
            if fence is None:
                fence = marker
            elif fence == marker:
                fence = None
            continue
        if fence is None and not stripped.startswith(">"):
            yield line


def parse_declared_area(body: str, areas: set[str]) -> tuple[bool, str | None]:
    """Return ``(present, value)`` for standalone ``Roadmap:`` lines.

    ``value`` is an area name or ``none`` when every declaration is valid and
    identical. It is ``None`` for invalid or conflicting declarations. Examples
    in fenced code and blockquotes are ignored.
    """
    present = False
    values = set()
    invalid = False
    for line in _body_lines_outside_quotes_and_fences(body):
        if not re.match(r"^Roadmap\s*:", line):
            continue
        present = True
        match = re.fullmatch(r"Roadmap:\s*(\S+)\s*", line)
        if match is None:
            invalid = True
            continue
        value = match.group(1)
        if value != "none" and value not in areas:
            invalid = True
        else:
            values.add(value)
    if invalid or len(values) != 1:
        return present, None
    return present, next(iter(values))


def parse_target_areas(body: str, areas: set[str]) -> set[str]:
    """Canonical roadmap focuses from valid ``tauceti-target:v1`` markers."""
    found = set()
    for match in _TARGET_MARKER.finditer(body or ""):
        try:
            focus = json.loads(match.group(1)).get("focus")
        except (json.JSONDecodeError, AttributeError):
            continue
        if focus in areas:
            found.add(focus)
    return found


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
    if is_pin_only(files):
        return NONE_LABEL

    declared_present, declared = parse_declared_area(body, areas)
    if declared_present and declared is None:
        return UNKNOWN_LABEL

    targets = parse_target_areas(body, areas)
    cited = parse_cited_areas(body, areas)
    indirect = targets | cited

    if declared is not None:
        if declared == "none":
            return NONE_LABEL if not indirect else UNKNOWN_LABEL
        return area_label(declared) if indirect <= {declared} else UNKNOWN_LABEL

    return area_label(next(iter(indirect))) if len(indirect) == 1 else UNKNOWN_LABEL


# --- roadmap area discovery ------------------------------------------------


def canonical_areas(roadmap_dir: pathlib.Path) -> set[str]:
    """Active and completed roadmap directory names under a checkout.

    At the repository root, active areas live under the inner
    `TauCetiRoadmap/` package and archived areas live under the sibling
    `Completed/` directory. Accepting the package directory itself remains
    useful for local one-area tests and older callers.
    """
    inner = roadmap_dir / "TauCetiRoadmap"
    if not inner.is_dir():
        return {
            p.name for p in roadmap_dir.iterdir()
            if p.is_dir() and (p / "README.md").is_file()
        }

    bases = [inner]
    completed = roadmap_dir / "Completed"
    if completed.is_dir():
        bases.append(completed)
    return {
        p.name for base in bases for p in base.iterdir()
        if p.is_dir() and (p / "README.md").is_file()
    }


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
        return NONE_COLOR, "No roadmap association (declared, infrastructure, or pin-only bump)"
    if name == UNKNOWN_LABEL:
        return UNKNOWN_COLOR, "Missing, invalid, or conflicting roadmap association"
    return AREA_COLOR, "PR declares the {} roadmap as its primary association".format(
        name[len("roadmap/"):])


NUDGE_MARKER = "<!--roadmap-label:nudge-->"
NUDGE_BODY = (
    NUDGE_MARKER + "\n"
    "I could not determine this PR's roadmap association, so I labelled it "
    "`roadmap/Unknown`. Please add one standalone line to the description:\n\n"
    "```text\nRoadmap: CanonicalAreaName\n```\n\n"
    "Use `Roadmap: none` for genuinely general, cross-cutting, infrastructure, "
    "or dependency work. Refactors need no fresh roadmap authorization, but should "
    "name the one roadmap chiefly motivating them. For new mathematics, this "
    "attribution line does not replace the [scope rubric's]"
    "(https://github.com/TauCetiProject/TauCetiReview/blob/main/rubrics/scope.md) "
    "requirement to cite the exact roadmap file and target."
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
    declared_present, declared = parse_declared_area(body, areas)
    if (is_infra(files) or is_pin_only(files)) and declared_present and declared not in {None, "none"}:
        reason = "infrastructure/empty diff" if is_infra(files) else "pin-only bump"
        print(
            f"::notice::Roadmap: {declared} is overridden by the {reason} classification"
        )
    if args.apply:
        apply_label(args.repo, args.pr, label, areas)
        if args.nudge and label == UNKNOWN_LABEL:
            nudge(args.repo, args.pr)
    return 0


def _run_backfill(args, areas) -> int:
    prs = json.loads(_gh([
        "pr", "list", "--repo", args.repo, "--state", "all",
        "--limit", str(args.limit),
        "--json", "number,title,body,files,state,labels",
    ]))
    from collections import Counter
    tally: Counter[str] = Counter()
    plan = []
    for p in prs:
        files = [f["path"] for f in p.get("files") or []]
        label = classify(p.get("title") or "", p.get("body") or "", files, areas)
        tally[label] += 1
        current = {
            item["name"] for item in p.get("labels") or []
            if item["name"].startswith("roadmap/")
        }
        plan.append((p["number"], label, current))
        print(f"#{p['number']}\t{p['state']}\t{label}\t{p.get('title','')}")

    failed: list[int] = []
    if args.apply:
        # A per-PR failure must not abandon the rest of the backfill; collect and
        # retry once at the end (transient API errors are already retried in _gh).
        for num, label, current in plan:
            if current == {label}:
                continue
            if current and current != {label} and not args.allow_relabel:
                print(
                    f"  - #{num}: preserving {', '.join(sorted(current))}; "
                    "pass --allow-relabel to change it",
                    file=sys.stderr,
                )
                continue
            try:
                apply_label(args.repo, num, label, areas)  # never nudges
            except Exception as e:  # noqa: BLE001 -- keep going, report at the end
                print(f"  ! #{num}: {e}", file=sys.stderr)
                failed.append(num)
        for num in list(failed):
            label = next(label for plan_num, label, _ in plan if plan_num == num)
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
    ap.add_argument(
        "--allow-relabel", action="store_true",
        help="with --backfill --apply, permit changing an existing roadmap/* label",
    )
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
