#!/usr/bin/env python3
"""Flag Mathlib namespaces recreated inside ``namespace TauCeti``.

The lint finds declarations under ``TauCeti.<Mathlib namespace>`` with an explicit argument of
the corresponding type, including explicit section variables used by the declaration. Mathlib
type namespaces are conservatively approximated by namespace commands in Mathlib's sources;
organisational namespaces, namespaces belonging to sort-valued Tau Ceti declarations
anywhere in the scanned source tree, and explicitly rooted declarations are ignored. Existing
findings are grandfathered by the grouped ``scripts/lint-dot-notation-baseline.txt``; update it
with ``--write-baseline``.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import pathlib
import re
import sys
from collections import Counter

from lean_source import (
    CLOSERS,
    Declaration,
    OPENERS,
    Scope,
    VariableBinding,
    declaration_returns_sort,
    declarations,
    include_commands,
    namespace_components,
    qualified_declarations,
    qualify,
    scopes,
    top_level_colon,
    top_level_arrow_parts,
    update_scope,
    variable_bindings,
)


# These organise declarations but do not themselves name receiver types. Names such as Set,
# Polynomial, and Nat are intentionally absent: their namespaces do name Mathlib types.
ORGANISATIONAL = {
    "AlgebraicGeometry", "Analysis", "CategoryTheory", "Combinatorics", "Function", "Geometry",
    "Lie", "LinearAlgebra", "MeasureTheory", "NumberTheory", "Order", "ProbabilityTheory",
    "RingTheory", "Topology",
}

OWN_DECLARATION_KEYWORDS = {"abbrev", "class", "def", "inductive", "opaque", "structure"}
TOP_LEVEL_CONNECTIVES = ("->", "→", "⟶", "⥤", "≃", "≅", "×", "⊕", "⊗", "↪", "↠")

# Common type notations whose underlying receiver type is not visible as an identifier in the
# source. Longer tokens must be tested first because several are extensions of shorter ones.
NOTATION_RECEIVERS = (
    ("→ₛₗᵢ[", "LinearIsometry"),
    ("≃ₛₗᵢ[", "LinearIsometryEquiv"),
    ("→ₗᵢ⋆[", "LinearIsometry"),
    ("≃ₗᵢ⋆[", "LinearIsometryEquiv"),
    ("→ₗᵢ[", "LinearIsometry"),
    ("≃ₗᵢ[", "LinearIsometryEquiv"),
    ("→+*", "RingHom"),
    ("≃+*", "RingEquiv"),
    ("→SL[", "ContinuousLinearMap"),
    ("≃SL[", "ContinuousLinearEquiv"),
    ("→L⋆[", "ContinuousLinearMap"),
    ("≃L⋆[", "ContinuousLinearEquiv"),
    ("→L[", "ContinuousLinearMap"),
    ("→ₗ[", "LinearMap"),
    ("→ₛₗ[", "LinearMap"),
    ("→ₗ⋆[", "LinearMap"),
    ("→ₐ[", "AlgHom"),
    ("≃ₐ[", "AlgEquiv"),
    ("≃L[", "ContinuousLinearEquiv"),
    ("≃ₗ[", "LinearEquiv"),
    ("≃ₛₗ[", "LinearEquiv"),
    ("≃ₗ⋆[", "LinearEquiv"),
    ("→A[", "ContinuousAlgHom"),
    ("≃A[", "ContinuousAlgEquiv"),
    ("→ₐc[", "BialgHom"),
    ("≃ₐc[", "BialgEquiv"),
    ("→ₗc[", "CoalgHom"),
    ("≃ₗc[", "CoalgEquiv"),
    ("→ₛₗ.[", "LinearPMap"),
    ("→ₗ.[", "LinearPMap"),
    ("→ₗ⁅", "LieHom"),
    ("≃ₗ⁅", "LieEquiv"),
    ("→ₐc", "BialgHom"),
    ("→ₗc", "CoalgHom"),
    ("≃ₘ^", "Diffeomorph"),
    ("≃ₘ⟮", "Diffeomorph"),
    ("≃ₘ[", "Diffeomorph"),
    ("≃ₜ*", "ContinuousMulEquiv"),
    ("≃ₜ+", "ContinuousAddEquiv"),
    ("≃ₜ", "Homeomorph"),
    ("→*", "MonoidHom"),
    ("→+", "AddMonoidHom"),
    ("→o", "OrderHom"),
    ("≃*", "MulEquiv"),
    ("≃+", "AddEquiv"),
    ("≃o", "OrderIso"),
    ("≃ᵢ", "IsometryEquiv"),
    ("⟶", "Hom"),
    ("⥤", "Functor"),
    ("≅", "Iso"),
    ("⊗[", "TensorProduct"),
    ("⊗", "TensorProduct"),
    ("×", "Prod"),
    ("⊕", "Sum"),
    ("↪", "Embedding"),
    ("≃", "Equiv"),
)

SPECIAL_NOTATION_RECEIVERS = (
    (re.compile(r"\[×[^]]*\]$"), "→L[", "ContinuousMultilinearMap"),
    (re.compile(r"\[⋀\^[^]]*\]$"), "→L[", "ContinuousAlternatingMap"),
    (re.compile(r"\[×[^]]*\]$"), "→ₗ[", "MultilinearMap"),
    (re.compile(r"\[⋀\^[^]]*\]$"), "→ₗ[", "AlternatingMap"),
)


@dataclasses.dataclass(frozen=True)
class Finding:
    """A violation's source path, one-based line, and fully qualified declaration display name."""

    path: pathlib.Path
    line: int
    declaration: str

    def render(self) -> str:
        return f"{self.path}:{self.line}: {self.declaration}"


def mathlib_namespaces(root: pathlib.Path) -> set[str]:
    """Collect individual namespace components occurring in Mathlib ``*.lean`` sources.

    The result is a conservative name set rather than a declaration-aware namespace hierarchy.
    """
    if not root.is_dir():
        raise FileNotFoundError(f"Mathlib source directory not found: {root}")
    names: set[str] = set()
    for path in root.rglob("*.lean"):
        raw = path.read_text(errors="ignore")
        if "namespace" not in raw:
            continue
        for _, kind, name in scopes(raw):
            if kind == "namespace" and name is not None:
                names.update(part for part in name.split(".") if part != "_root_")
    return names


def own_declaration_paths(sources: dict[pathlib.Path, str]) -> set[tuple[str, ...]]:
    """Return fully qualified paths of explicitly sort-valued Tau Ceti declarations.

    Structures, classes, inductives, and definitions annotated with a result ending in ``Type``,
    ``Sort``, or ``Prop`` suppress their exact namespaces, including uses from other files.
    """
    owned: set[tuple[str, ...]] = set()
    for text in sources.values():
        names = qualified_declarations(
            text,
            keep=lambda declaration: (
                declaration.keyword in OWN_DECLARATION_KEYWORDS
                and declaration_returns_sort(declaration)
            ),
        )
        for name in names:
            path = name.split(".")
            if path and path[0] == "TauCeti":
                owned.add(tuple(path))
    return owned


def _top_level_notation_receiver(binder_type: str) -> str | None:
    """Return the receiver namespace encoded by a common top-level type notation, if any."""
    stripped = binder_type.lstrip()
    continuous_map_prefix = re.match(r"C\s*\(", stripped) is not None

    depth = 0
    position = 0
    while position < len(binder_type):
        char = binder_type[position]
        if char in OPENERS:
            depth += 1
        elif char in CLOSERS:
            depth -= 1
        elif depth == 0:
            prefix = binder_type[:position].rstrip()
            for pattern, token, receiver in SPECIAL_NOTATION_RECEIVERS:
                if pattern.search(prefix) and binder_type.startswith(token, position):
                    return receiver
            for token, receiver in NOTATION_RECEIVERS:
                if binder_type.startswith(token, position):
                    end = position + len(token)
                    if (token.endswith(("[", "⟮", "⁅", "^")) or end == len(binder_type)
                            or binder_type[end].isspace()):
                        return receiver
            if any(binder_type.startswith(token, position) for token in TOP_LEVEL_CONNECTIVES):
                return None
        position += 1
    return "ContinuousMap" if continuous_map_prefix else None


def _binder_has_type(binder: str, namespace: str) -> bool:
    colon = top_level_colon(binder)
    if colon is None:
        return False
    binder_type = binder[colon + 1:].lstrip()
    if _top_level_notation_receiver(binder_type) == namespace:
        return True
    qualified = rf"(?:_root_\.)?(?:[\w']+\.)*{re.escape(namespace)}\b"
    match = re.match(rf"@?{qualified}", binder_type)
    if match is None or binder_type[match.end():].startswith("."):
        return False
    depth = 0
    for position, char in enumerate(binder_type):
        if char in OPENERS:
            depth += 1
        elif char in CLOSERS:
            depth -= 1
        elif depth == 0 and any(binder_type.startswith(op, position)
                                for op in TOP_LEVEL_CONNECTIVES):
            return False
    return True


def _result_has_argument_type(header: str, namespace: str) -> bool:
    """Whether a top-level arrow in the result type has a domain named ``namespace``."""
    colon = top_level_colon(header)
    if colon is None:
        return False
    domains = top_level_arrow_parts(header[colon + 1:])[:-1]
    return any(_binder_has_type(f"_ : {domain}", namespace) for domain in domains)


def find_violations(
    sources: dict[pathlib.Path, str], mathlib_namespace_names: set[str]
) -> list[Finding]:
    """Find recreated Mathlib type namespaces in a mapping of Tau Ceti source files.

    The textual analysis combines declaration, scope, explicit section-variable, and include/omit
    events. A finding requires a Mathlib namespace candidate and a corresponding explicit receiver
    type; rooted declarations and namespaces owned by Tau Ceti are excluded.
    """
    findings: list[Finding] = []
    owned = own_declaration_paths(sources)
    for path, text in sorted(sources.items()):
        parsed = declarations(text)
        events: list[tuple[int, str, object]] = [
            (position, "scope", (kind, name)) for position, kind, name in scopes(text)
        ]
        events.extend((declaration.position, "declaration", declaration) for declaration in parsed)
        events.extend((position, "variables", bindings)
                      for position, bindings in variable_bindings(text))
        events.extend((position, "include", (action, names, one_shot))
                      for position, action, names, one_shot in include_commands(text))
        events.sort(key=lambda event: event[0])

        stack: list[Scope] = []
        active_variables: list[tuple[int, VariableBinding]] = []
        included_by_depth: list[set[str]] = [set()]
        one_shot_includes: list[tuple[str, set[str]]] = []
        for _, event_kind, payload in events:
            if event_kind == "scope":
                kind, name = payload  # type: ignore[misc]
                old_depth = len(stack)
                update_scope(stack, kind, name)
                if len(stack) > old_depth:
                    included_by_depth.extend(
                        set(included_by_depth[-1]) for _ in range(len(stack) - old_depth))
                elif len(stack) < old_depth:
                    del included_by_depth[len(stack) + 1:]
                active_variables = [(depth, binding) for depth, binding in active_variables
                                    if depth <= len(stack)]
                continue

            if event_kind == "variables":
                assert isinstance(payload, list)
                active_variables.extend(
                    (len(stack), binding) for binding in payload if binding.kind == "explicit"
                )
                continue

            if event_kind == "include":
                action, names, one_shot = payload  # type: ignore[misc]
                if one_shot:
                    one_shot_includes.append((action, names))
                elif action == "include":
                    included_by_depth[-1].update(names)
                else:
                    included_by_depth[-1].difference_update(names)
                continue

            declaration = payload
            assert isinstance(declaration, Declaration)
            included_names = set(included_by_depth[-1])
            for action, names in one_shot_includes:
                if action == "include":
                    included_names.update(names)
                else:
                    included_names.difference_update(names)
            one_shot_includes.clear()
            namespaces = namespace_components(stack)
            if not namespaces or namespaces[0] != "TauCeti":
                continue
            if declaration.name is not None and declaration.name.startswith("_root_."):
                continue
            if declaration.name is not None:
                declaration_path = qualify(declaration.name, stack).split(".")
                if declaration_path[:len(namespaces)] != namespaces:
                    continue
                name_prefix = declaration_path[len(namespaces):-1]
            else:
                name_prefix = []
            candidate_path = [*namespaces, *name_prefix]
            candidates = [namespace for index, namespace in enumerate(candidate_path[1:], start=1)
                          if namespace in mathlib_namespace_names
                          and namespace not in ORGANISATIONAL
                          and tuple(candidate_path[:index + 1]) not in owned]
            current_variables: dict[str, str] = {}
            for _, binding in active_variables:
                current_variables[binding.name] = binding.binder
            matching = [
                namespace
                for namespace in candidates
                if any(_binder_has_type(binder, namespace) for binder in declaration.binders)
                or _result_has_argument_type(declaration.header, namespace)
                or any(_binder_has_type(binder, namespace)
                       and (name in included_names
                            or re.search(rf"(?<![\w']){re.escape(name)}(?![\w'])",
                                         declaration.header))
                       for name, binder in current_variables.items())
            ]
            if not matching:
                continue

            if declaration.name is None:
                normalized = " ".join(declaration.header.split())
                digest = hashlib.sha256(normalized.encode()).hexdigest()[:12]
                declared_name = f"<anonymous instance {digest}>"
            else:
                declared_name = declaration.name
            qualified_name = qualify(declared_name, stack)
            line = text.count("\n", 0, declaration.position) + 1
            findings.append(Finding(path, line, qualified_name))

    return sorted(findings, key=lambda finding: (str(finding.path), finding.line, finding.declaration))


def read_baseline(path: pathlib.Path) -> list[str]:
    """Read the grouped baseline and return its declaration names, preserving duplicates.

    Each nonempty line is ``source-path<TAB>JSON-array-of-qualified-declaration-names``.
    """
    declarations: list[str] = []
    for line in path.read_text().splitlines():
        try:
            _, encoded = line.split("\t", 1)
            names = json.loads(encoded)
        except (ValueError, json.JSONDecodeError) as error:
            raise ValueError(f"malformed dot-notation baseline entry: {line}") from error
        if not isinstance(names, list) or not all(isinstance(name, str) for name in names):
            raise ValueError(f"malformed dot-notation baseline entry: {line}")
        declarations.extend(names)
    return declarations


def write_baseline(path: pathlib.Path, findings: list[Finding]) -> None:
    """Write findings in deterministic source-grouped JSON-line baseline format."""
    grouped: dict[pathlib.Path, list[str]] = {}
    for finding in findings:
        grouped.setdefault(finding.path, []).append(finding.declaration)
    path.write_text("".join(
        f"{source}\t{json.dumps(names, ensure_ascii=False, separators=(',', ':'))}\n"
        for source, names in grouped.items()))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", type=pathlib.Path, default=pathlib.Path(
        "scripts/lint-dot-notation-baseline.txt"))
    parser.add_argument("--mathlib-root", type=pathlib.Path, default=pathlib.Path(
        ".lake/packages/mathlib/Mathlib"))
    parser.add_argument("--source-root", type=pathlib.Path, default=pathlib.Path("TauCeti"))
    parser.add_argument("--write-baseline", action="store_true")
    args = parser.parse_args(argv)

    try:
        namespace_names = mathlib_namespaces(args.mathlib_root)
    except FileNotFoundError as error:
        print(f"lint-dot-notation: error: {error}", file=sys.stderr)
        return 2
    if not args.source_root.is_dir():
        print(f"lint-dot-notation: error: source directory not found: {args.source_root}",
              file=sys.stderr)
        return 2

    sources = {path: path.read_text(errors="ignore")
               for path in args.source_root.rglob("*.lean")}
    found = find_violations(sources, namespace_names)

    if args.write_baseline:
        write_baseline(args.baseline, found)
        print(f"lint-dot-notation: wrote {len(found)} baseline entries")
        return 0
    if not args.baseline.is_file():
        print(f"lint-dot-notation: error: baseline not found: {args.baseline}", file=sys.stderr)
        return 2

    try:
        known = Counter(read_baseline(args.baseline))
    except ValueError as error:
        print(f"lint-dot-notation: error: {error}", file=sys.stderr)
        return 2
    current = Counter(finding.declaration for finding in found)
    new_counts = current - known
    new: list[Finding] = []
    for finding in found:
        if new_counts[finding.declaration]:
            new.append(finding)
            new_counts[finding.declaration] -= 1
    fixed = sum((known - current).values())

    print(
        f"lint-dot-notation: {len(found)} total, {sum(known.values())} grandfathered, "
        f"{len(new)} new, {fixed} ratchetable"
    )
    if fixed:
        print("lint-dot-notation: baseline entries no longer found; regenerate with --write-baseline")
    if not new:
        return 0

    print("\nA Mathlib type's namespace is nested inside `namespace TauCeti`, so dot")
    print("notation on that type does not elaborate. Move the declaration to the type's")
    print("root namespace. Watch for `open` and `variable` commands that must move with it.\n")
    print("If the namespace belongs to a Tau Ceti type, give its definition an explicit")
    print("result sort such as `: Type _` or `: Prop`.\n")
    for finding in new:
        print(f"  {finding.render()}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
