#!/usr/bin/env python3
"""Report tracked Tau Ceti shims whose replacement exists in pinned Mathlib.

The registry in ``TauCeti/mathlib-shims.json`` is AI-owned metadata kept out of module docstrings.
Each entry names one or more Tau Ceti source files and a concrete Mathlib declaration or module.
Exact replacements and broader landing sentinels carry different guidance. The default invocation
is report-only; ``--fail-on-available`` turns an exact finding into an autonomous PR gate that
hands the source or bump PR to a Tau Ceti worker. Malformed metadata or an unavailable Lean
environment is always an infrastructure error.
"""

from __future__ import annotations

import argparse
import dataclasses
import functools
import importlib.util
import json
import os
import pathlib
import re
import subprocess
import sys
from collections.abc import Iterable, Sequence


DECLARATION = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*")
MODULE = re.compile(r"Mathlib(?:\.[^\W\d][\w']*)+")
PROBE_PREFIX = "TAUCETI_MATHLIB_DECL\t"
SELF_DECLARED = re.compile(r"\btemporary\b.{0,40}\bshim\b", re.IGNORECASE | re.DOTALL)
SELF_DECLARED_OBSOLESCENCE = re.compile(
    r"\bwhen\s+Mathlib\b.{0,160}\b(?:deleted?|removed?)\b", re.IGNORECASE | re.DOTALL
)
SELF_DECLARED_VENDORING = re.compile(
    r"\bmigrate\s+to\s+Mathlib\s+and\s+delete\b", re.IGNORECASE
)
SELF_DECLARED_PORT = re.compile(
    r"\b(?:this\s+)?copy\b.{0,80}\bdeleted\b.{0,80}\bMathlib\b", re.IGNORECASE | re.DOTALL
)
NEGATED_SELF_DECLARATION = re.compile(
    r"(?:\*{1,2})?(?:\brather\s+than|\bnot)(?:\*{1,2})?\s+"
    r"(?:an?\s+)?(?:\*{1,2})?\s*$",
    re.IGNORECASE,
)


@dataclasses.dataclass(frozen=True)
class ShimGroup:
    """Source files sharing the same possible Mathlib replacements."""

    sources: tuple[pathlib.Path, ...]
    declarations: tuple[str, ...]
    modules: tuple[str, ...]
    note: str
    speculative: bool = False
    landing_sentinel: bool = False
    local_declarations: tuple[str, ...] = ()


@dataclasses.dataclass(frozen=True)
class AvailableReplacement:
    """A tracked source and the replacement targets already present in Mathlib."""

    source: pathlib.Path
    targets: tuple[str, ...]
    note: str
    speculative: bool = False
    landing_sentinel: bool = False


def _string_list(value: object, field: str, entry: int) -> tuple[str, ...]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError(f"entry {entry}: {field} must be a list of strings")
    return tuple(value)


def load_registry(
    path: pathlib.Path, repo_root: pathlib.Path, *, require_sources: bool = True
) -> tuple[ShimGroup, ...]:
    """Read and validate the shim registry, including every tracked source path."""

    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"cannot read {path}: {error}") from error
    if not isinstance(raw, list):
        raise ValueError("the shim registry must be a JSON list")

    groups: list[ShimGroup] = []
    seen_sources: set[pathlib.Path] = set()
    for index, item in enumerate(raw, start=1):
        if not isinstance(item, dict):
            raise ValueError(f"entry {index}: expected an object")
        sources_raw = _string_list(item.get("sources"), "sources", index)
        declarations = _string_list(item.get("declarations", []), "declarations", index)
        modules = _string_list(item.get("modules", []), "modules", index)
        local_declarations = _string_list(
            item.get("local_declarations", []), "local_declarations", index
        )
        note = item.get("note", "")
        speculative = item.get("speculative", False)
        landing_sentinel = item.get("landing_sentinel", False)
        if not isinstance(note, str):
            raise ValueError(f"entry {index}: note must be a string")
        if not isinstance(speculative, bool):
            raise ValueError(f"entry {index}: speculative must be a boolean")
        if not isinstance(landing_sentinel, bool):
            raise ValueError(f"entry {index}: landing_sentinel must be a boolean")
        if not sources_raw:
            raise ValueError(f"entry {index}: sources must not be empty")
        if not declarations and not modules:
            raise ValueError(f"entry {index}: name at least one declaration or module")
        for declaration in declarations:
            if DECLARATION.fullmatch(declaration) is None:
                raise ValueError(f"entry {index}: invalid declaration name {declaration!r}")
        for declaration in local_declarations:
            if DECLARATION.fullmatch(declaration) is None:
                raise ValueError(f"entry {index}: invalid local declaration name {declaration!r}")
        for module in modules:
            if MODULE.fullmatch(module) is None:
                raise ValueError(f"entry {index}: invalid Mathlib module name {module!r}")

        sources: list[pathlib.Path] = []
        for source_raw in sources_raw:
            source = pathlib.Path(source_raw)
            if source.is_absolute() or ".." in source.parts or source.suffix != ".lean" \
                    or not source.parts or source.parts[0] != "TauCeti":
                raise ValueError(f"entry {index}: source must be a TauCeti/*.lean path: {source}")
            if source in seen_sources:
                raise ValueError(f"entry {index}: duplicate source {source}")
            if require_sources and not (repo_root / source).is_file():
                raise ValueError(f"entry {index}: tracked source does not exist: {source}")
            seen_sources.add(source)
            sources.append(source)
        if (declarations or modules) and not speculative and not landing_sentinel \
                and not local_declarations:
            raise ValueError(
                f"entry {index}: exact probes require local_declarations"
            )
        groups.append(ShimGroup(
            tuple(sources), declarations, modules, note, speculative, landing_sentinel,
            local_declarations,
        ))
    return tuple(groups)


def find_self_declared_shims(source_root: pathlib.Path) -> set[pathlib.Path]:
    """Find prose that declares a temporary/pending Mathlib relationship.

    The registry remains authoritative after process prose is removed from module docstrings. This
    scan is one-way enforcement: newly added self-declarations must be registered, while removing
    old narrative does not discard the maintenance obligation recorded in the registry.
    """

    repo_root = source_root.parent
    found: set[pathlib.Path] = set()
    for source in source_root.rglob("*.lean"):
        text = source.read_text(encoding="utf-8")
        for match in SELF_DECLARED.finditer(text):
            prefix = text[max(0, match.start() - 80):match.start()]
            if NEGATED_SELF_DECLARATION.search(prefix) is None:
                found.add(source.relative_to(repo_root))
                break
        else:
            if SELF_DECLARED_OBSOLESCENCE.search(text) is not None \
                    or SELF_DECLARED_VENDORING.search(text) is not None \
                    or SELF_DECLARED_PORT.search(text) is not None:
                found.add(source.relative_to(repo_root))
    return found


def validate_registry_coverage(groups: Sequence[ShimGroup], source_root: pathlib.Path) -> None:
    """Reject self-declared shims that do not name a machine-checkable replacement."""

    tracked = {source for group in groups for source in group.sources}
    untracked = sorted(find_self_declared_shims(source_root) - tracked)
    if untracked:
        rendered = "\n".join(f"  {source}" for source in untracked)
        raise ValueError(
            "self-declared Mathlib shims are missing from TauCeti/mathlib-shims.json:\n"
            f"{rendered}"
        )


def validate_local_declarations(groups: Sequence[ShimGroup], repo_root: pathlib.Path) -> None:
    """Require every ratchet key to name a declaration in its registered sources."""

    invalid: list[tuple[ShimGroup, tuple[str, ...]]] = []
    for group in groups:
        declared: set[str] = set()
        for source in group.sources:
            declared.update(source_declarations(repo_root / source))
        missing = tuple(sorted(set(group.local_declarations) - declared))
        if missing:
            invalid.append((group, missing))
    if invalid:
        rendered = "\n".join(
            f"  {', '.join(map(str, group.sources))}: {', '.join(missing)}"
            for group, missing in invalid
        )
        raise ValueError(
            "registered local_declarations are absent from their tracked sources:\n"
            f"{rendered}"
        )


def groups_by_source(groups: Sequence[ShimGroup]) -> dict[pathlib.Path, ShimGroup]:
    """Expand registry groups into their unique source-file keys."""

    return {source: group for group in groups for source in group.sources}


@functools.cache
def lean_source_parser():
    """Load the trusted command-level Lean parser shared with the dot-notation lint."""

    path = pathlib.Path(__file__).with_name("lint-dot-notation.py")
    spec = importlib.util.spec_from_file_location("tauceti_lint_dot_notation", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load Lean source parser: {path}")
    parser = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = parser
    spec.loader.exec_module(parser)
    return parser


def source_declarations(path: pathlib.Path) -> set[str]:
    """Return fully qualified command-level declaration names from one Lean source."""

    parser = lean_source_parser()
    text = path.read_text(encoding="utf-8")
    code = parser.strip_comments_and_strings(text)
    events: list[tuple[int, str, object]] = [
        (position, "scope", (kind, name)) for position, kind, name in parser.scopes(text)
    ]
    events.extend(
        (declaration.position, "declaration", declaration)
        for declaration in parser.declarations(text)
    )
    events.extend(
        (match.start(), "compatibility", match.group("name"))
        for match in re.finditer(
            r"(?m)^\s*(?:public\s+|private\s+|protected\s+)?(?:alias|axiom)\s+"
            r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)",
            code,
        )
    )
    events.sort(key=lambda event: event[0])
    stack: list[object] = []
    found: set[str] = set()
    for _, kind, payload in events:
        if kind == "scope":
            scope_kind, name = payload
            parser._update_scope(stack, scope_kind, name)
            continue
        if kind == "compatibility":
            declaration_name = payload
        else:
            declaration = payload
            if declaration.name is None:
                continue
            declaration_name = declaration.name
        namespaces = [component for scope in stack for component in scope.components]
        if declaration_name.startswith("_root_."):
            parts = declaration_name.removeprefix("_root_.").split(".")
        else:
            parts = [*namespaces, *declaration_name.split(".")]
        found.add(".".join(parts))
    return found


def tree_declarations(source_root: pathlib.Path) -> set[str]:
    """Collect command-level declaration names from the current Tau Ceti tree."""

    found: set[str] = set()
    for path in source_root.rglob("*.lean"):
        found.update(source_declarations(path))
    return found


def validate_registry_ratchet(
    groups: Sequence[ShimGroup], base_groups: Sequence[ShimGroup], repo_root: pathlib.Path
) -> None:
    """Keep a base obligation until its registered local shim surface is removed."""

    current = groups_by_source(groups)
    weakened: list[pathlib.Path] = []
    declared: set[str] | None = None
    for source, base in groups_by_source(base_groups).items():
        candidate = current.get(source)
        flags_weakened = candidate is not None and (
            (not base.speculative and candidate.speculative)
            or (not base.landing_sentinel and candidate.landing_sentinel)
        )
        probes_weakened = candidate is None or (
            not set(base.declarations) <= set(candidate.declarations)
            or not set(base.modules) <= set(candidate.modules)
        )
        if flags_weakened:
            weakened.append(source)
        elif probes_weakened:
            if not base.local_declarations:
                weakened.append(source)
                continue
            if declared is None:
                declared = tree_declarations(repo_root / "TauCeti")
            if declared.intersection(base.local_declarations):
                weakened.append(source)
    if weakened:
        rendered = "\n".join(f"  {source}" for source in sorted(weakened))
        raise ValueError(
            "base shim obligations were weakened while their registered local surface remains; "
            "migrate the local declarations (or delete/re-home a file-wide module shim) before "
            "removing its probes or changing it to an audit-only sentinel:\n"
            f"{rendered}"
        )


def only_new_or_changed_groups(
    groups: Sequence[ShimGroup], base_groups: Sequence[ShimGroup]
) -> tuple[ShimGroup, ...]:
    """Restrict a source PR probe to registry obligations it introduced or changed."""

    def signature(group: ShimGroup) -> tuple[object, ...]:
        return (
            group.declarations,
            group.modules,
            group.speculative,
            group.landing_sentinel,
            group.local_declarations,
        )

    base = groups_by_source(base_groups)
    changed: list[ShimGroup] = []
    for group in groups:
        sources = tuple(
            source for source in group.sources
            if source not in base or signature(group) != signature(base[source])
        )
        if sources:
            changed.append(dataclasses.replace(group, sources=sources))
    return tuple(changed)


def render_declaration_probe(declarations: Iterable[str]) -> str:
    """Build a Lean command that checks names in the fully imported Mathlib environment."""

    names = sorted(set(declarations))
    lines = [
        "import Mathlib",
        "open Lean Elab Command",
        "elab \"#checkMathlibShims\" : command => do",
        "  let env ← getEnv",
    ]
    if not names:
        lines.append("  pure ()")
    for name in names:
        lines.extend([
            f"  if env.contains `{name} then",
            f"    liftIO <| IO.println \"{PROBE_PREFIX}{name}\"",
        ])
    lines.append("#checkMathlibShims")
    return "\n".join(lines) + "\n"


def parse_probe_output(output: str) -> set[str]:
    """Extract declaration names emitted by ``render_declaration_probe``."""

    return {
        line.removeprefix(PROBE_PREFIX)
        for line in output.splitlines()
        if line.startswith(PROBE_PREFIX)
    }


def probe_declarations(declarations: Iterable[str], lake_root: pathlib.Path) -> set[str]:
    """Return declarations found in pinned Mathlib's Lean environment."""

    names = tuple(sorted(set(declarations)))
    if not names:
        return set()
    source = render_declaration_probe(names)
    completed = subprocess.run(
        ["lake", "env", "lean", "/dev/stdin"],
        cwd=lake_root,
        input=source,
        encoding="utf-8",
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip() or "Lean exited nonzero"
        raise RuntimeError(f"could not inspect pinned Mathlib declarations:\n{detail}")
    return parse_probe_output(completed.stdout)


def module_path(mathlib_root: pathlib.Path, module: str) -> pathlib.Path:
    """Translate a Mathlib module name to its source path."""

    return mathlib_root.joinpath(*module.split(".")).with_suffix(".lean")


def available_replacements(
    groups: Sequence[ShimGroup], found_declarations: set[str], mathlib_root: pathlib.Path
) -> tuple[AvailableReplacement, ...]:
    """Pair each source with targets already available in pinned Mathlib."""

    if any(group.modules for group in groups) and not (mathlib_root / "Mathlib").is_dir():
        raise RuntimeError(f"Mathlib source tree does not exist: {mathlib_root}")

    available: list[AvailableReplacement] = []
    for group in groups:
        targets = tuple(
            [f"declaration {name}" for name in group.declarations if name in found_declarations]
            + [f"module {name}" for name in group.modules
               if module_path(mathlib_root, name).is_file()]
        )
        if targets:
            available.extend(
                AvailableReplacement(
                    source, targets, group.note, group.speculative, group.landing_sentinel
                )
                for source in group.sources
            )
    return tuple(available)


def markdown_summary(
    groups: Sequence[ShimGroup], available: Sequence[AvailableReplacement], *,
    blocking: bool = False,
) -> str:
    """Render the check's GitHub Actions summary."""

    tracked = sum(len(group.sources) for group in groups)
    lines = ["## Expired Mathlib shim check", "",
             f"Tracked **{tracked}** Tau Ceti source files.", ""]
    if not available:
        lines.append("No configured replacement target exists in the pinned dependency.")
        return "\n".join(lines) + "\n"
    disposition = (
        "This PR is blocked until its worker migrates each affected source."
        if blocking else "Audit each affected source; this report does not fail the build."
    )
    lines.extend([
        f"Found upstream triggers affecting **{len(available)}** source files. {disposition}",
        "",
        "| Tau Ceti source | Available upstream trigger | Migration guidance | Context |",
        "|---|---|---|---|",
    ])
    for replacement in available:
        targets = ", ".join(f"`{target}`" for target in replacement.targets)
        note = replacement.note.replace("|", "\\|").replace("\n", " ")
        if replacement.speculative:
            note = f"Speculative target name; {note}"
        if replacement.landing_sentinel:
            guidance = ("Audit against the landed stack; migrate only declarations with canonical "
                        "counterparts and preserve or re-home source-only API.")
        else:
            guidance = "Migrate to the canonical target and delete only the superseded surface."
        lines.append(f"| `{replacement.source}` | {targets} | {guidance} | {note} |")
    return "\n".join(lines) + "\n"


def warning_message(replacement: AvailableReplacement) -> str:
    """Render precise annotation advice without declaring a whole source obsolete."""

    targets = ", ".join(replacement.targets)
    speculative = " [speculative target name]" if replacement.speculative else ""
    if replacement.landing_sentinel:
        advice = ("audit this source against the landed stack; migrate only declarations with "
                  "canonical counterparts and preserve or re-home source-only API")
    else:
        advice = "migrate to the canonical target and delete only the superseded surface"
    return f"Pinned Mathlib now provides {targets}; {advice} ({replacement.note}){speculative}"


def blocks_bump(replacement: AvailableReplacement) -> bool:
    """Whether this trigger is a concrete migration rather than an audit-only sentinel."""

    return not replacement.speculative and not replacement.landing_sentinel


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=pathlib.Path,
                        default=pathlib.Path(__file__).resolve().parent.parent)
    parser.add_argument("--manifest", type=pathlib.Path)
    parser.add_argument("--base-manifest", type=pathlib.Path,
                        help="trusted base registry whose live obligations may not be weakened")
    parser.add_argument("--mathlib-root", type=pathlib.Path)
    parser.add_argument("--lake-root", type=pathlib.Path)
    parser.add_argument("--coverage-only", action="store_true",
                        help="validate source coverage without probing Mathlib")
    parser.add_argument("--only-new", action="store_true",
                        help="probe only entries added or changed relative to --base-manifest")
    parser.add_argument("--fail-on-available", action="store_true",
                        help="exit 3 when Mathlib provides a configured exact replacement")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    repo_root = args.repo_root.resolve()
    manifest = (args.manifest or repo_root / "TauCeti/mathlib-shims.json").resolve()
    mathlib_root = (args.mathlib_root or repo_root / ".lake/packages/mathlib").resolve()
    lake_root = (args.lake_root or repo_root).resolve()
    try:
        groups = load_registry(manifest, repo_root)
        validate_registry_coverage(groups, repo_root / "TauCeti")
        validate_local_declarations(groups, repo_root)
        base_groups: tuple[ShimGroup, ...] = ()
        if args.base_manifest is not None:
            if not args.base_manifest.is_file():
                raise ValueError(f"base registry does not exist: {args.base_manifest}")
            base_groups = load_registry(
                args.base_manifest.resolve(), repo_root, require_sources=False
            )
            validate_registry_ratchet(groups, base_groups, repo_root)
        if args.coverage_only:
            print("check-expired-mathlib-shims: registry covers all self-declared shims")
            return 0
        if args.only_new:
            if args.base_manifest is None:
                raise ValueError("--only-new requires --base-manifest")
            probe_groups = only_new_or_changed_groups(groups, base_groups)
        else:
            probe_groups = groups
        declarations = (name for group in probe_groups for name in group.declarations)
        found = probe_declarations(declarations, lake_root)
        available = available_replacements(probe_groups, found, mathlib_root)
    except Exception as error:
        print(f"check-expired-mathlib-shims: error: {error}", file=sys.stderr)
        return 2

    tracked = sum(len(group.sources) for group in groups)
    blocking = tuple(replacement for replacement in available if blocks_bump(replacement))
    print(f"check-expired-mathlib-shims: {tracked} tracked files, "
          f"{len(available)} with available replacements ({len(blocking)} blocking)")
    for replacement in available:
        annotation = "error" if args.fail_on_available and blocks_bump(replacement) else "warning"
        print(f"::{annotation} file={replacement.source}::{warning_message(replacement)}")

    summary = markdown_summary(
        groups, available, blocking=bool(blocking) and args.fail_on_available
    )
    if summary_path := os.environ.get("GITHUB_STEP_SUMMARY"):
        with pathlib.Path(summary_path).open("a", encoding="utf-8") as stream:
            stream.write(summary)
    elif available:
        print(summary)
    return 3 if args.fail_on_available and blocking else 0


if __name__ == "__main__":
    sys.exit(main())
