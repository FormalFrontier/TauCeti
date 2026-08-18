#!/usr/bin/env python3
"""Shared command-level Lean source parser and dot-notation namespace lint.

The parser is intentionally syntactic and is shared by repository hygiene checks. The dot-notation
lint finds declarations under ``TauCeti.<Mathlib namespace>`` with an explicit argument of
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
from collections.abc import Callable, Iterable


# These organise declarations but do not themselves name receiver types. Names such as Set,
# Polynomial, and Nat are intentionally absent: their namespaces do name Mathlib types.
ORGANISATIONAL = {
    "AlgebraicGeometry", "Analysis", "CategoryTheory", "Combinatorics", "Function", "Geometry",
    "Lie", "LinearAlgebra", "MeasureTheory", "NumberTheory", "Order", "ProbabilityTheory",
    "RingTheory", "Topology",
}

DECLARATION_KEYWORDS = {
    "abbrev", "class", "def", "inductive", "instance", "lemma", "opaque", "structure",
    "theorem",
}
OWN_DECLARATION_KEYWORDS = {"abbrev", "class", "def", "inductive", "opaque", "structure"}
MODIFIERS = {
    "local", "noncomputable", "nonrec", "partial", "private", "protected", "public", "scoped",
    "unsafe",
}
IDENTIFIER = re.compile(r"(?:_root_\.)?[\w']+(?:\.[\w']+)*")
WORD = re.compile(r"[A-Za-z_][\w']*")
PAIRS = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
OPENERS = set(PAIRS)
CLOSERS = set(PAIRS.values())
NAMESPACE = re.compile(
    r"(?m)^(?:(?:public|private|protected|noncomputable)\s+)*namespace\s+([\w'.]+)"
)
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
class Declaration:
    """A parsed command header, including source offset, keyword, name, binders, and result text."""

    keyword: str
    name: str | None
    binders: tuple[str, ...]
    header: str
    position: int


@dataclasses.dataclass(frozen=True)
class Scope:
    """A namespace, section, or mutual scope and the namespace components it contributes."""

    kind: str
    name: str | None
    components: tuple[str, ...]

    def matches(self, end_name: str) -> bool:
        return self.name == end_name or (self.kind == "namespace" and bool(self.components)
                                         and self.components[-1] == end_name)


@dataclasses.dataclass(frozen=True)
class Finding:
    """A violation's source path, one-based line, and fully qualified declaration display name."""

    path: pathlib.Path
    line: int
    declaration: str

    def render(self) -> str:
        return f"{self.path}:{self.line}: {self.declaration}"


@dataclasses.dataclass(frozen=True)
class VariableBinding:
    """A section-variable name paired with its complete textual binder for receiver matching."""

    name: str
    binder: str


def strip_comments_and_strings(text: str) -> str:
    """Blank comments and strings while preserving offsets and newlines."""
    chars = list(text)
    i = 0
    block_depth = 0
    in_string = False
    while i < len(chars):
        if block_depth:
            if text.startswith("/-", i):
                chars[i] = chars[i + 1] = " "
                block_depth += 1
                i += 2
            elif text.startswith("-/", i):
                chars[i] = chars[i + 1] = " "
                block_depth -= 1
                i += 2
            else:
                if chars[i] != "\n":
                    chars[i] = " "
                i += 1
        elif in_string:
            if chars[i] == "\\" and i + 1 < len(chars):
                chars[i] = " "
                if chars[i + 1] != "\n":
                    chars[i + 1] = " "
                i += 2
            else:
                if chars[i] == '"':
                    in_string = False
                if chars[i] != "\n":
                    chars[i] = " "
                i += 1
        elif text.startswith("--", i):
            while i < len(chars) and chars[i] != "\n":
                chars[i] = " "
                i += 1
        elif text.startswith("/-", i):
            chars[i] = chars[i + 1] = " "
            block_depth = 1
            i += 2
        elif chars[i] == '"':
            chars[i] = " "
            in_string = True
            i += 1
        elif chars[i] == "'" and (i == 0 or not (
                chars[i - 1].isalnum() or chars[i - 1] in "_'")) and i + 2 < len(chars) and (
                chars[i + 1] == "\\" or chars[i + 2] == "'"):
            end = i + 2
            while end < len(chars) and chars[end] not in "'\n":
                end += 1
            if end < len(chars) and chars[end] == "'":
                while i <= end:
                    chars[i] = " "
                    i += 1
            else:
                i += 1
        else:
            i += 1
    return "".join(chars)


def _skip_horizontal(text: str, position: int) -> int:
    while position < len(text) and text[position] in " \t\r":
        position += 1
    return position


def _skip_balanced(text: str, position: int) -> int:
    if position >= len(text) or text[position] not in PAIRS:
        return position
    stack = [PAIRS[text[position]]]
    position += 1
    while position < len(text) and stack:
        char = text[position]
        if char in PAIRS:
            stack.append(PAIRS[char])
        elif char == stack[-1]:
            stack.pop()
        position += 1
    return position


def _command_prefix(text: str, line_start: int) -> tuple[int, str] | None:
    """Return the declaration keyword position and keyword for a command at ``line_start``."""
    position = _skip_horizontal(text, line_start)
    while text.startswith("@[", position):
        position = _skip_balanced(text, position + 1)
        while position < len(text) and text[position].isspace():
            position += 1

    while True:
        match = WORD.match(text, position)
        if not match or match.group() not in MODIFIERS:
            break
        position = _skip_horizontal(text, match.end())

    match = WORD.match(text, position)
    if match and match.group() in DECLARATION_KEYWORDS:
        return position, match.group()
    return None


def _top_level_colon(group: str) -> int | None:
    depth = 0
    for i, char in enumerate(group):
        if char in OPENERS:
            depth += 1
        elif char in CLOSERS:
            depth -= 1
        elif char == ":" and depth == 0 and not group.startswith(":=", i):
            return i
    return None


def _declaration_tail(text: str, position: int) -> tuple[tuple[str, ...], str]:
    """Collect declaration binders and the header through its body introducer."""
    binders: list[str] = []
    start = position
    while position < len(text):
        position = _skip_horizontal(text, position)
        if text.startswith(":=", position):
            break
        word = WORD.match(text, position)
        if word and word.group() == "where":
            break
        char = text[position]
        if char == ":" or char == "|":
            header_end = position
            depth = 0
            while header_end < len(text):
                if text.startswith(":=", header_end) and depth == 0:
                    break
                next_word = WORD.match(text, header_end)
                if next_word and next_word.group() == "where" and depth == 0:
                    break
                current = text[header_end]
                if current in OPENERS:
                    depth += 1
                elif current in CLOSERS:
                    depth -= 1
                elif current == "|" and depth == 0:
                    break
                header_end += 1
            return tuple(binders), text[start:header_end]
        if char in OPENERS:
            end = _skip_balanced(text, position)
            group = text[position + 1:end - 1]
            if char == "(" and _top_level_colon(group) is not None:
                binders.append(group)
            position = end
        elif char == "\n":
            if _command_prefix(text, position + 1) is not None:
                break
            position += 1
        else:
            position += 1
    return tuple(binders), text[start:position]


def declarations(text: str) -> list[Declaration]:
    """Parse top-level declaration headers from comment/string-stripped Lean source.

    This is deliberately a command-level approximation: it records explicit parenthesized
    binders and the header up to ``:=``, ``where``, or an equation clause, without parsing terms.
    """
    code = strip_comments_and_strings(text)
    found: dict[int, Declaration] = {}
    line_start = 0
    while line_start < len(code):
        prefix = _command_prefix(code, line_start)
        if prefix is not None:
            keyword_position, keyword = prefix
            position = _skip_horizontal(code, keyword_position + len(keyword))
            name: str | None = None
            if keyword == "instance" and code.startswith("(priority", position):
                position = _skip_horizontal(code, _skip_balanced(code, position))
            if keyword != "instance" or (position < len(code) and code[position] not in "({[:"):
                match = IDENTIFIER.match(code, position)
                if match:
                    name = match.group()
                    position = match.end()
            binders, header = _declaration_tail(code, position)
            found[keyword_position] = Declaration(keyword, name, binders, header, keyword_position)
        newline = code.find("\n", line_start)
        line_start = len(code) if newline == -1 else newline + 1
    return [found[position] for position in sorted(found)]


def scopes(text: str) -> list[tuple[int, str, str | None]]:
    """Return positions and names of namespace, section, mutual, and end commands.

    Only standalone command lines are recognized; the events are consumed in source order by the
    namespace-stack approximation.
    """
    code = strip_comments_and_strings(text)
    pattern = re.compile(
        r"(?m)^(?:(?:public|private|protected|noncomputable)\s+)*"
        r"(?P<kind>namespace|section|mutual|end)(?:\s+(?P<name>[\w'.]+))?[ \t]*$"
    )
    return [(m.start(), m.group("kind"), m.group("name")) for m in pattern.finditer(code)]


def variable_bindings(text: str) -> list[tuple[int, list[VariableBinding]]]:
    """Return explicit parenthesized section-variable bindings grouped by command position.

    Implicit and instance-implicit variables are intentionally omitted because they cannot be
    dot-notation receivers.
    """
    code = strip_comments_and_strings(text)
    pattern = re.compile(r"(?m)^variable\b[^\n]*(?:\n[ \t]+[^\n]*)*")
    events: list[tuple[int, list[VariableBinding]]] = []
    for match in pattern.finditer(code):
        body = match.group()
        position = len("variable")
        bindings: list[VariableBinding] = []
        while position < len(body):
            if body[position] in OPENERS:
                opener = body[position]
                end = _skip_balanced(body, position)
                group = body[position + 1:end - 1]
                colon = _top_level_colon(group)
                if opener == "(" and colon is not None:
                    names = re.findall(r"(?<![\w'])[\w']+(?![\w'])", group[:colon])
                    bindings.extend(VariableBinding(name, group) for name in names if name != "_")
                position = end
            else:
                position += 1
        if bindings:
            events.append((match.start(), bindings))
    return events


def _include_commands(text: str) -> list[tuple[int, str, set[str], bool]]:
    """Return scoped include/omit operations as position, action, bare names, and one-shot flag."""
    code = strip_comments_and_strings(text)
    pattern = re.compile(r"(?m)^[ \t]*(?P<action>include|omit)\s+(?P<body>[^\n]+)$")
    commands: list[tuple[int, str, set[str], bool]] = []
    for match in pattern.finditer(code):
        body = match.group("body").rstrip()
        one_shot = re.search(r"(?:^|\s)in$", body) is not None
        if one_shot:
            body = re.sub(r"(?:^|\s)in$", "", body).rstrip()
        names: set[str] = set()
        position = 0
        while position < len(body):
            if body[position] in OPENERS:
                position = _skip_balanced(body, position)
                continue
            name = re.match(r"[\w']+", body[position:])
            if name is not None:
                names.add(name.group())
                position += len(name.group())
            else:
                position += 1
        commands.append((match.start(), match.group("action"), names, one_shot))
    return commands


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
        text = strip_comments_and_strings(raw)
        for match in NAMESPACE.finditer(text):
            names.update(part for part in match.group(1).split(".") if part != "_root_")
    return names


def update_scope(stack: list[Scope], kind: str, name: str | None) -> None:
    """Apply one namespace/section/mutual/end event to a scope stack."""

    if kind == "namespace":
        assert name is not None
        stack.append(Scope(kind, name, tuple(name.split("."))))
    elif kind in {"section", "mutual"}:
        stack.append(Scope(kind, name, ()))
    elif name is None:
        if stack:
            stack.pop()
    else:
        for index in range(len(stack) - 1, -1, -1):
            if stack[index].matches(name):
                del stack[index:]
                break


def qualified_declarations(
    text: str, *, extra_declarations: Iterable[tuple[int, str]] = (),
    keep: Callable[[Declaration], bool] | None = None,
) -> set[str]:
    """Return fully qualified command-level names, with optional extra declaration events."""

    events: list[tuple[int, str, object]] = [
        (position, "scope", (kind, name)) for position, kind, name in scopes(text)
    ]
    events.extend(
        (declaration.position, "declaration", declaration)
        for declaration in declarations(text)
    )
    events.extend((position, "extra", name) for position, name in extra_declarations)
    events.sort(key=lambda event: event[0])
    stack: list[Scope] = []
    found: set[str] = set()
    for _, kind, payload in events:
        if kind == "scope":
            scope_kind, name = payload  # type: ignore[misc]
            update_scope(stack, scope_kind, name)
            continue
        if kind == "declaration":
            declaration = payload
            assert isinstance(declaration, Declaration)
            if declaration.name is None or (keep is not None and not keep(declaration)):
                continue
            declaration_name = declaration.name
        else:
            assert isinstance(payload, str)
            declaration_name = payload
        namespaces = [component for scope in stack for component in scope.components]
        if declaration_name.startswith("_root_."):
            parts = declaration_name.removeprefix("_root_.").split(".")
        else:
            parts = [*namespaces, *declaration_name.split(".")]
        found.add(".".join(parts))
    return found


def _declaration_returns_sort(declaration: Declaration) -> bool:
    """Whether a declaration is syntactically certain to create a type or proposition."""
    if declaration.keyword in {"class", "inductive", "structure"}:
        return True
    if declaration.keyword not in {"abbrev", "def", "opaque"}:
        return False
    colon = _top_level_colon(declaration.header)
    if colon is None:
        return False
    return _expression_returns_sort(declaration.header[colon + 1:])


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
                and _declaration_returns_sort(declaration)
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
    colon = _top_level_colon(binder)
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


def _top_level_arrow_parts(text: str) -> list[str]:
    """Split ``text`` at top-level ASCII or Unicode function arrows."""
    depth = 0
    part_start = 0
    parts: list[str] = []
    position = 0
    while position < len(text):
        char = text[position]
        if char in OPENERS:
            depth += 1
        elif char in CLOSERS:
            depth -= 1
        elif depth == 0 and (char == "→" or text.startswith("->", position)):
            parts.append(text[part_start:position])
            position += 1 if char == "→" else 2
            part_start = position
            continue
        position += 1
    parts.append(text[part_start:])
    return parts


def _expression_returns_sort(text: str) -> bool:
    """Whether a result expression ends in ``Prop``, ``Sort``, or ``Type`` syntactically."""
    expression = text.strip()
    while expression.startswith("(") and _skip_balanced(expression, 0) == len(expression):
        expression = expression[1:-1].strip()

    if expression.startswith(("∀", "Π")):
        depth = 0
        for position, char in enumerate(expression):
            if char in OPENERS:
                depth += 1
            elif char in CLOSERS:
                depth -= 1
            elif char == "," and depth == 0:
                return _expression_returns_sort(expression[position + 1:])
        return False

    parts = _top_level_arrow_parts(expression)
    if len(parts) > 1:
        return _expression_returns_sort(parts[-1])
    return re.match(r"(?:Prop|Sort|Type)\b", expression) is not None


def _result_has_argument_type(header: str, namespace: str) -> bool:
    """Whether a top-level arrow in the result type has a domain named ``namespace``."""
    colon = _top_level_colon(header)
    if colon is None:
        return False
    domains = _top_level_arrow_parts(header[colon + 1:])[:-1]
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
                      for position, action, names, one_shot in _include_commands(text))
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
                active_variables.extend((len(stack), binding) for binding in payload)
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
            namespaces = [component for scope in stack for component in scope.components]
            if not namespaces or namespaces[0] != "TauCeti":
                continue
            if declaration.name is not None and declaration.name.startswith("_root_."):
                continue
            name_prefix = declaration.name.split(".")[:-1] if declaration.name else []
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
            qualified_name = ".".join([*namespaces, declared_name])
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
