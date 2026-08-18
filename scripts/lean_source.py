#!/usr/bin/env python3
"""Syntactic parsing helpers for command-level Lean source.

``declarations`` parses declaration headers, ``scopes`` and ``update_scope`` approximate the
namespace stack, ``variable_bindings`` parses explicit section variables, and
``qualified_declarations`` combines declaration and scope events into qualified names. This is
not a Lean parser: comments and strings are blanked while source offsets are preserved, and terms
are inspected only as text. The dot-notation lint is currently the sole production consumer; the
module exists so later hygiene checks can reuse the parser without importing lint policy.
"""

from __future__ import annotations

import dataclasses
import re
from collections.abc import Callable


DECLARATION_KEYWORDS = {
    "abbrev", "class", "def", "inductive", "instance", "lemma", "opaque", "structure",
    "theorem",
}
MODIFIERS = {
    "local", "noncomputable", "nonrec", "partial", "private", "protected", "public", "scoped",
    "unsafe",
}
IDENTIFIER = re.compile(r"(?:_root_\.)?[\w']+(?:\.[\w']+)*")
WORD = re.compile(r"[A-Za-z_][\w']*")
PAIRS = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
OPENERS = set(PAIRS)
CLOSERS = set(PAIRS.values())


@dataclasses.dataclass(frozen=True)
class Declaration:
    """A declaration's offset, keyword, name, binders, and header through its body introducer."""

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


def skip_balanced(text: str, position: int) -> int:
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
        position = skip_balanced(text, position + 1)
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


def top_level_colon(group: str) -> int | None:
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
            end = skip_balanced(text, position)
            group = text[position + 1:end - 1]
            if char == "(" and top_level_colon(group) is not None:
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
                position = _skip_horizontal(code, skip_balanced(code, position))
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
                end = skip_balanced(body, position)
                group = body[position + 1:end - 1]
                colon = top_level_colon(group)
                if opener == "(" and colon is not None:
                    names = re.findall(r"(?<![\w'])[\w']+(?![\w'])", group[:colon])
                    bindings.extend(VariableBinding(name, group) for name in names if name != "_")
                position = end
            else:
                position += 1
        if bindings:
            events.append((match.start(), bindings))
    return events


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
    text: str, *, keep: Callable[[Declaration], bool] | None = None,
) -> set[str]:
    """Return qualified names of parsed, named declarations accepted by ``keep``.

    The optional predicate receives each parsed declaration; omit it to retain every named
    declaration. Namespace events qualify ordinary names, while ``_root_.`` names remain rooted.
    Anonymous instances and any other declarations without a parsed name are omitted.
    """

    events: list[tuple[int, str, object]] = [
        (position, "scope", (kind, name)) for position, kind, name in scopes(text)
    ]
    events.extend(
        (declaration.position, "declaration", declaration)
        for declaration in declarations(text)
    )
    events.sort(key=lambda event: event[0])
    stack: list[Scope] = []
    found: set[str] = set()
    for _, kind, payload in events:
        if kind == "scope":
            scope_kind, name = payload  # type: ignore[misc]
            update_scope(stack, scope_kind, name)
            continue
        declaration = payload
        assert isinstance(declaration, Declaration)
        if declaration.name is None or (keep is not None and not keep(declaration)):
            continue
        declaration_name = declaration.name
        namespaces = [component for scope in stack for component in scope.components]
        if declaration_name.startswith("_root_."):
            parts = declaration_name.removeprefix("_root_.").split(".")
        else:
            parts = [*namespaces, *declaration_name.split(".")]
        found.add(".".join(parts))
    return found
