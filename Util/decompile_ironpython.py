#!/usr/bin/env python3
"""Invert IronPython 2.7 cached-code C# into readable Python source.

The input C# must be produced by ILSpy from a ``DLRCachedCode`` assembly.  The
script combines that syntax tree with the cached global-name attribute and the
``PythonOps.MakeFunctionCode`` metadata extracted by
``Util/index_eas_recovery.py``.  It never loads or executes a recovered module.

This is deliberately a semantic decompiler, not a C# pretty-printer.  Dynamic
call sites are paired with their serialized binders and converted back to
Python member, call, operator, index, and slice expressions.  Compiler frame,
stack-trace, module-publication, and call-site-cache scaffolding is omitted.
"""

from __future__ import annotations

import argparse
import ast
from collections import Counter
from dataclasses import dataclass, field
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any, Iterable, Iterator, Sequence

try:
    from tree_sitter import Language, Node, Parser
    import tree_sitter_c_sharp
except ImportError as error:  # pragma: no cover - exercised by CLI installation
    raise SystemExit(
        "missing parser dependency; install Util/requirements-ironpython-decompiler.txt"
    ) from error


EXPRESSION_OPERATORS = {
    "Add": "+",
    "Subtract": "-",
    "Multiply": "*",
    "Divide": "/",
    "Modulo": "%",
    "Power": "**",
    "And": "&",
    "Or": "|",
    "ExclusiveOr": "^",
    "LeftShift": "<<",
    "RightShift": ">>",
    "LessThan": "<",
    "LessThanOrEqual": "<=",
    "GreaterThan": ">",
    "GreaterThanOrEqual": ">=",
    "Equal": "==",
    "NotEqual": "!=",
    "AddAssign": "+=",
    "SubtractAssign": "-=",
    "MultiplyAssign": "*=",
    "DivideAssign": "/=",
    "ModuloAssign": "%=",
    "AndAssign": "&=",
    "OrAssign": "|=",
    "ExclusiveOrAssign": "^=",
    "LeftShiftAssign": "<<=",
    "RightShiftAssign": ">>=",
}

UNARY_OPERATORS = {
    "Not": "not ",
    "IsFalse": "not ",
    "Negate": "-",
    "UnaryPlus": "+",
    "Positive": "+",
    "OnesComplement": "~",
}

# Numeric values are fixed by Src/IronPython/Runtime/Binding/
# PythonOperationKind.cs in IronPython 2.7.12.
PYTHON_OPERATION_KINDS = {
    5: "Contains",
    6: "Length",
    7: "Compare",
    8: "DivMod",
    9: "AbsoluteValue",
    10: "Positive",
    11: "Negate",
    12: "OnesComplement",
    13: "GetItem",
    14: "SetItem",
    15: "DeleteItem",
    16: "IsFalse",
    17: "Not",
    18: "GetEnumeratorForIteration",
    19: "Add",
    20: "Subtract",
    21: "Power",
    22: "Multiply",
    23: "FloorDivide",
    24: "Divide",
    25: "TrueDivide",
    26: "Modulo",
    27: "LeftShift",
    28: "RightShift",
    29: "BitwiseAnd",
    30: "BitwiseOr",
    31: "ExclusiveOr",
}

OPERATION_OPERATORS = {
    "Add": "+",
    "Subtract": "-",
    "Power": "**",
    "Multiply": "*",
    "FloorDivide": "//",
    "Divide": "/",
    "TrueDivide": "/",
    "Modulo": "%",
    "LeftShift": "<<",
    "RightShift": ">>",
    "BitwiseAnd": "&",
    "BitwiseOr": "|",
    "ExclusiveOr": "^",
}

CSHARP_BINARY_OPERATORS = {
    "&&": "and",
    "||": "or",
    "==": "==",
    "!=": "!=",
    "<": "<",
    "<=": "<=",
    ">": ">",
    ">=": ">=",
    "+": "+",
    "-": "-",
    "*": "*",
    "/": "/",
    "%": "%",
    "&": "&",
    "|": "|",
    "^": "^",
    "<<": "<<",
    ">>": ">>",
}

SCAFFOLD_CALLS = {
    "LightExceptions.CheckAndThrow",
    "PythonOps.BuildExceptionInfo",
    "PythonOps.ExceptionHandled",
    "PythonOps.ForLoopDispose",
    "PythonOps.ModuleStarted",
    "PythonOps.PublishModule",
    "PythonOps.PushFrame",
    "PythonOps.RemoveModule",
    "PythonOps.RestoreCurrentException",
    "PythonOps.SaveCurrentException",
    "PythonOps.SetCurrentException",
    "PythonOps.UpdateStackTrace",
    "GC.KeepAlive",
}

CONTEXT_IDENTIFIERS = {
    "_0024globalContext",
    "_0024parentContext",
    "globalContext",
    "parentContext",
    "context",
    "context2",
    "context3",
}


def decode_identifier(value: str) -> str:
    """Decode ILSpy's escaped CLR identifier spelling."""
    value = re.sub(
        r"_([0-9A-Fa-f]{4})",
        lambda match: chr(int(match.group(1), 16)),
        value,
    )
    if value.startswith("$"):
        value = value[1:]
    # ``$`` is legal in CLR-generated identifiers but never in Python 2.
    return value.replace("$", "_")


def decode_csharp_string(value: str) -> str:
    value = value.strip()
    if value.startswith('@"') and value.endswith('"'):
        return value[2:-1].replace('""', '"')
    if value.startswith('"') and value.endswith('"'):
        return ast.literal_eval(value)
    raise ValueError("not a C# string literal: %s" % value[:80])


def split_balanced(text: str, separator: str = ",") -> list[str]:
    """Split at top-level separators in generated C# expressions."""
    result: list[str] = []
    start = 0
    stack: list[str] = []
    quote: str | None = None
    verbatim = False
    index = 0
    pairs = {"(": ")", "[": "]", "{": "}", "<": ">"}
    while index < len(text):
        char = text[index]
        nxt = text[index + 1] if index + 1 < len(text) else ""
        if quote is not None:
            if verbatim and char == '"' and nxt == '"':
                index += 2
                continue
            if not verbatim and char == "\\":
                index += 2
                continue
            if char == quote:
                quote = None
                verbatim = False
            index += 1
            continue
        if char in ('"', "'"):
            quote = char
            verbatim = char == '"' and index > 0 and text[index - 1] == "@"
        elif char in pairs:
            stack.append(pairs[char])
        elif stack and char == stack[-1]:
            stack.pop()
        elif char == separator and not stack:
            result.append(text[start:index].strip())
            start = index + 1
        index += 1
    result.append(text[start:].strip())
    return result


def python_repr(value: Any) -> str:
    if isinstance(value, str):
        return repr(value)
    return repr(value)


def unwrap_single(text: str, opening: str = "(", closing: str = ")") -> str:
    text = text.strip()
    if not (text.startswith(opening) and text.endswith(closing)):
        return text
    depth = 0
    quote: str | None = None
    for index, char in enumerate(text):
        if quote:
            if char == "\\":
                continue
            if char == quote:
                quote = None
            continue
        if char in ('"', "'"):
            quote = char
        elif char == opening:
            depth += 1
        elif char == closing:
            depth -= 1
            if depth == 0 and index != len(text) - 1:
                return text
    return text[1:-1].strip() if depth == 0 else text


@dataclass(frozen=True)
class Binder:
    index: int
    kind: str
    name: str | None = None
    operation: str | None = None
    call_arguments: tuple[tuple[str, str | None], ...] = ()
    bool_result: bool = False
    initializer: str = ""


@dataclass
class Scope:
    name: str
    target_method: str | None
    argument_names: list[str]
    variable_names: list[str]
    global_names: list[str]
    free_variables: list[str]
    cell_variables: list[str]
    flags: set[str]
    documentation: str | None
    source_start_index: int
    source_end_index: int
    source_lines: list[int]
    code_index: int | None = None
    parent: Scope | None = None
    children: list[Scope] = field(default_factory=list)

    @property
    def is_class(self) -> bool:
        return not self.argument_names and "__module__" in self.variable_names

    @property
    def is_lambda(self) -> bool:
        return self.name.startswith("<lambda$")

    @property
    def is_comprehension(self) -> bool:
        return self.name in {"<genexpr>", "<listcomp>", "<dictcomp>", "<setcomp>"}

    @property
    def is_generator(self) -> bool:
        return "Generator" in self.flags


@dataclass
class Expr:
    text: str
    precedence: int = 100
    scope_ref: Scope | None = None
    defaults: list[str] = field(default_factory=list)
    decorators: list[str] = field(default_factory=list)
    statement: str | None = None
    unresolved: bool = False

    def parenthesized(self, threshold: int) -> str:
        return "(%s)" % self.text if self.precedence < threshold else self.text


@dataclass
class Diagnostic:
    module: str
    scope: str
    line: int | None
    kind: str
    detail: str


@dataclass
class LightState:
    current_line: int | None = None
    pending: Expr | None = None
    emitted_on_line: bool = False


class CSharpDocument:
    def __init__(self, path: Path):
        self.path = path
        self.data = path.read_bytes()
        parser = Parser(Language(tree_sitter_c_sharp.language()))
        self.tree = parser.parse(self.data)
        if self.tree.root_node.has_error:
            raise ValueError("C# syntax tree contains an error: %s" % path)
        self.methods: dict[str, list[Node]] = {}
        self._index_methods(self.tree.root_node)

    def text(self, node: Node | None) -> str:
        if node is None:
            return ""
        return self.data[node.start_byte:node.end_byte].decode("utf-8", "replace")

    def _index_methods(self, node: Node) -> None:
        if node.type == "method_declaration":
            name = node.child_by_field_name("name")
            if name is not None:
                self.methods.setdefault(self.text(name), []).append(node)
        for child in node.named_children:
            self._index_methods(child)

    def descendants(self, node: Node, kind: str) -> Iterator[Node]:
        if node.type == kind:
            yield node
        for child in node.named_children:
            yield from self.descendants(child, kind)


class PythonWriter:
    def __init__(self):
        self.lines: list[str] = []
        self.indent = 0

    def write(self, text: str = "") -> None:
        if "\n" in text:
            for line in text.splitlines():
                self.write(line)
            return
        self.lines.append("    " * self.indent + text if text else "")

    def block(self, header: str):
        writer = self

        class Block:
            def __enter__(self_nonlocal):
                writer.write(header)
                writer.indent += 1

            def __exit__(self_nonlocal, exc_type, exc, traceback):
                writer.indent -= 1

        return Block()

    def render(self) -> str:
        lines = list(self.lines)
        while lines and not lines[-1]:
            lines.pop()
        return "\n".join(lines) + "\n"


class ScopeContext:
    def __init__(self, decompiler: IronPythonDecompiler, scope: Scope | None):
        self.decompiler = decompiler
        self.scope = scope
        self.current_line: int | None = None
        self.aliases: dict[str, str] = {}
        self.identifier_aliases: dict[str, str] = {}
        self.identifier_versions: dict[str, list[tuple[int, str]]] = {}
        self.assigned_names: set[str] = set()
        self.pending_names: list[str] = []
        self.emitted_children: set[int] = set()
        self.loop_enumerators: dict[str, Expr] = {}
        self.uninitialized: set[str] = set()
        self.import_modules: dict[str, tuple[str, int]] = {}
        self.line_identifiers: set[str] = set()
        self.tuple_slots: dict[int, str] = {}
        self.generator_comprehensions: dict[str, tuple[str, str]] = {}
        self.generator_loop_depth = 0
        self.generator_resume_processed: set[tuple[str, int]] = set()
        self.generator_consumed_enumerators: set[str] = set()
        self.generator_temp_slots: dict[int, str] = {}
        self.generator_consumed_sections: set[int] = set()
        # ILSpy reuses generated local names such as ``target`` and ``target2``
        # in disjoint nested blocks.  Binder lookup therefore has to be lexical;
        # a flat name -> binder map can associate calls in a try body with an
        # identically named delegate from its catch handler.
        self.delegate_binders: dict[str, list[tuple[int, int, Binder]]] = {}
        self.skip_statement_bytes: set[int] = set()
        self.semantic_statements = 0
        if scope is not None:
            for name in scope.argument_names:
                self.identifier_aliases[self.cs_name(name)] = name
                self.assigned_names.add(name)
            excluded = set(scope.argument_names)
            excluded.update(child.name for child in scope.children if not child.is_lambda)
            self.pending_names = [
                name for name in scope.variable_names
                if name not in excluded and not name.startswith("<")
                and name not in {"__doc__", "__module__"}
            ]

    @staticmethod
    def cs_name(name: str) -> str:
        return name.replace("$", "_0024_")

    @staticmethod
    def canonical(value: str) -> str:
        return re.sub(r"\s+", "", value)

    def add_alias(self, expression: str, name: str) -> None:
        self.aliases[self.canonical(expression)] = name
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", expression.strip()):
            self.identifier_aliases[expression.strip()] = name
        self.assigned_names.add(name)
        if name in self.pending_names:
            self.pending_names.remove(name)

    def lookup_alias(self, expression: str) -> str | None:
        return self.aliases.get(self.canonical(expression))

    def add_identifier_version(
        self,
        identifier: str,
        position: int,
        value: str,
    ) -> None:
        versions = self.identifier_versions.setdefault(identifier, [])
        versions[:] = [item for item in versions if item[0] != position]
        versions.append((position, value))
        self.identifier_aliases[identifier] = value

    def identifier_at(self, identifier: str, position: int) -> str | None:
        versions = [
            item for item in self.identifier_versions.get(identifier, ())
            if item[0] <= position
        ]
        if versions:
            return max(versions, key=lambda item: item[0])[1]
        return self.identifier_aliases.get(identifier)

    def allocate_name(self, identifier: str, preferred: str | None = None) -> str:
        if identifier in self.identifier_aliases:
            return self.identifier_aliases[identifier]
        if preferred and preferred not in self.assigned_names:
            name = preferred
        elif self.pending_names:
            name = self.pending_names.pop(0)
        else:
            name = decode_identifier(identifier)
        self.identifier_aliases[identifier] = name
        self.assigned_names.add(name)
        return name

    def allocate_synthetic(self, prefix: str) -> str:
        unavailable = set(self.assigned_names)
        unavailable.update(self.pending_names)
        if self.scope is not None:
            unavailable.update(self.scope.argument_names)
            unavailable.update(self.scope.variable_names)
        index = 1
        candidate = prefix
        while candidate in unavailable:
            index += 1
            candidate = "%s%d" % (prefix, index)
        self.assigned_names.add(candidate)
        return candidate

    def add_delegate_binder(
        self,
        identifier: str,
        start_byte: int,
        end_byte: int,
        binder: Binder,
    ) -> None:
        self.delegate_binders.setdefault(identifier, []).append(
            (start_byte, end_byte, binder)
        )

    def delegate_binder_at(self, identifier: str, byte_offset: int) -> Binder | None:
        candidates = [
            item for item in self.delegate_binders.get(identifier, ())
            if item[0] <= byte_offset < item[1]
        ]
        if not candidates:
            # Labels produced for light-exception control flow can move a use
            # just outside the lexical block that assigned the delegate.  The
            # nearest preceding assignment is still the active CallSite cache
            # in IL order; later reassignments delimit subsequent uses.
            candidates = [
                item for item in self.delegate_binders.get(identifier, ())
                if item[0] <= byte_offset
            ]
        if not candidates:
            return None
        return max(candidates, key=lambda item: item[0])[2]


class IronPythonDecompiler:
    def __init__(
        self,
        module_name: str,
        document: CSharpDocument,
        metadata: dict[str, Any],
        functions: dict[str, Any],
    ):
        self.module_name = module_name
        self.document = document
        self.metadata = metadata
        self.function_data = functions
        module = metadata["cached_modules"][0]
        self.module_method = module["delegate_method"].replace("$", "_0024")
        self.global_names = list(module["global_names"])
        self.binders: dict[int, Binder] = {}
        self.scopes: list[Scope] = []
        self.scope_by_method: dict[str, list[Scope]] = {}
        self.scope_by_code_index: dict[int, Scope] = {}
        self.inline_scope_nodes: dict[int, Node] = {}
        self.constant_nodes: dict[int, Node] = {}
        self.diagnostics: list[Diagnostic] = []
        self.stats: Counter[str] = Counter()
        self._load_scopes()
        self._extract_initializers()
        self._build_scope_tree()

    def diagnostic(
        self,
        context: ScopeContext,
        kind: str,
        detail: str,
    ) -> None:
        self.diagnostics.append(Diagnostic(
            self.module_name,
            context.scope.name if context.scope else "<module>",
            context.current_line,
            kind,
            detail[:500],
        ))
        self.stats["unresolved"] += 1

    @staticmethod
    def _is_python_assignment_target(text: str, augmented: bool = False) -> bool:
        try:
            ast.parse("%s %s 0\n" % (text, "+=" if augmented else "="))
        except (SyntaxError, ValueError, TypeError):
            return False
        return True

    @classmethod
    def _is_python_assignment_statement(cls, text: str) -> bool:
        stripped = text.strip()
        if stripped.startswith("del "):
            return cls._is_python_assignment_target(stripped[4:])
        match = re.match(
            r"^(.+?)\s+(\*\*=|//=|<<=|>>=|\+=|-=|\*=|/=|%=|&=|\|=|\^=)\s+.+$",
            stripped,
            re.S,
        )
        if match is not None:
            return cls._is_python_assignment_target(match.group(1), augmented=True)
        match = re.match(r"^(.+?)\s=\s.+$", stripped, re.S)
        if match is not None:
            return cls._is_python_assignment_target(match.group(1))
        return True

    def _valid_assignment_target(
        self,
        target: str,
        identifier: str,
        context: ScopeContext,
    ) -> str:
        if self._is_python_assignment_target(target):
            return target
        context.identifier_aliases.pop(identifier, None)
        decoded = decode_identifier(identifier)
        preferred = decoded if self._is_python_assignment_target(decoded) else None
        target = context.allocate_name(identifier, preferred)
        if self._is_python_assignment_target(target):
            self.stats["invalid_assignment_targets_repaired"] += 1
            return target
        target = context.allocate_synthetic("_item")
        context.identifier_aliases[identifier] = target
        self.stats["invalid_assignment_targets_repaired"] += 1
        return target

    @classmethod
    def _is_python_loop_target(cls, text: str) -> bool:
        stripped = text.strip()
        if stripped.startswith("(") and stripped.endswith(")"):
            values = split_balanced(stripped[1:-1])
            return bool(values) and all(cls._is_python_loop_target(item) for item in values)
        return re.fullmatch(
            r"[A-Za-z_][A-Za-z0-9_]*(?:(?:\.[A-Za-z_][A-Za-z0-9_]*)|(?:\[[^\[\]]+\]))*",
            stripped,
        ) is not None

    def _valid_loop_target(
        self,
        target: str,
        identifier: str,
        context: ScopeContext,
    ) -> str:
        if self._is_python_loop_target(target):
            return target
        context.identifier_aliases.pop(identifier, None)
        decoded = decode_identifier(identifier)
        preferred = decoded if self._is_python_loop_target(decoded) else None
        repaired = context.allocate_name(identifier, preferred)
        if not self._is_python_loop_target(repaired):
            repaired = context.allocate_synthetic("_item")
            context.identifier_aliases[identifier] = repaired
        self.stats["invalid_loop_targets_repaired"] += 1
        return repaired

    def _load_scopes(self) -> None:
        for item in self.function_data.get("functions", []):
            scope = Scope(
                name=item["name"],
                target_method=item.get("target_method"),
                argument_names=list(item.get("argument_names") or []),
                variable_names=list(item.get("variable_names") or []),
                global_names=list(item.get("global_names") or []),
                free_variables=list(item.get("free_variables") or []),
                cell_variables=list(item.get("cell_variables") or []),
                flags=set(item.get("flags") or []),
                documentation=item.get("documentation"),
                source_start_index=item["source_start_index"],
                source_end_index=item["source_end_index"],
                source_lines=list(item.get("source_lines") or []),
            )
            self.scopes.append(scope)
            if scope.target_method:
                self.scope_by_method.setdefault(scope.target_method, []).append(scope)

    def _build_scope_tree(self) -> None:
        for scope in self.scopes:
            candidates = [
                other for other in self.scopes
                if other is not scope
                and other.source_start_index <= scope.source_start_index
                and scope.source_end_index <= other.source_end_index
            ]
            if candidates:
                scope.parent = min(
                    candidates,
                    key=lambda item: item.source_end_index - item.source_start_index,
                )
                scope.parent.children.append(scope)
        for scope in self.scopes:
            scope.children.sort(key=lambda item: item.source_start_index)

    def _extract_initializers(self) -> None:
        nodes = self.document.methods.get(self.module_method)
        if not nodes:
            # ILSpy sometimes appends/escapes a leading source-method character.
            candidates = [
                values for name, values in self.document.methods.items()
                if name.startswith(self.module_method)
            ]
            nodes = candidates[0] if candidates else None
        if not nodes:
            raise ValueError("cached module method not found: %s" % self.module_method)
        method = nodes[0]
        body = method.child_by_field_name("body")
        if body is None:
            raise ValueError("cached module method has no body")
        for statement in self.document.descendants(body, "expression_statement"):
            raw = self.document.text(statement).strip().rstrip(";")
            match = re.match(
                r"(?:strongBox\.Value|array)\[(\d+)\]\s*=\s*(.*)\Z",
                raw,
                re.S,
            )
            if not match:
                continue
            index = int(match.group(1))
            value = match.group(2).strip()
            if "PythonOps.MakeFunctionCode(" in value:
                self._associate_function_code(index, value, statement)
            elif "CallSite<" in value and ".Create(" in value:
                binder = self._parse_binder(index, value)
                if binder is not None:
                    self.binders[index] = binder
            else:
                assignment = statement.named_children[0] if statement.named_children else None
                if assignment is not None and assignment.type == "assignment_expression":
                    right = assignment.child_by_field_name("right") or assignment.named_children[-1]
                    self.constant_nodes[index] = right

    def _associate_function_code(self, index: int, value: str, statement: Node) -> None:
        match = re.search(r"PythonOps\.MakeFunctionCode\([^,]+,\s*(\"(?:\\.|[^\"])*\")", value)
        if not match:
            return
        name = decode_csharp_string(match.group(1))
        candidates = [scope for scope in self.scopes if scope.name == name and scope.code_index is None]
        if not candidates:
            return
        # Initializers are emitted in reverse source nesting/order.  Target
        # method text disambiguates repeated conventional names when present.
        target = None
        target_match = re.findall(r"&([A-Za-z0-9_]+)", value)
        if target_match:
            for candidate in candidates:
                if candidate.target_method == target_match[-1]:
                    target = candidate
                    break
        target = target or candidates[-1]
        target.code_index = index
        self.scope_by_code_index[index] = target
        if target.target_method is None:
            anonymous = next(
                self.document.descendants(statement, "anonymous_method_expression"),
                None,
            )
            if anonymous is not None:
                body = anonymous.child_by_field_name("body")
                if body is None:
                    body = next(
                        (child for child in anonymous.named_children if child.type == "block"),
                        None,
                    )
                if body is not None:
                    self.inline_scope_nodes[id(target)] = body

    def _parse_binder(self, index: int, value: str) -> Binder | None:
        def string_argument(pattern: str) -> str | None:
            match = re.search(pattern, value, re.S)
            return decode_csharp_string(match.group(1)) if match else None

        def token_argument(pattern: str) -> str | None:
            match = re.search(pattern, value, re.S)
            return match.group(1) if match else None

        if "MakeComboAction" in value:
            operation = token_argument(r"MakeBinaryOperationAction\([^,]+,\s*ExpressionType\.([A-Za-z]+)")
            if operation:
                return Binder(index, "binary", operation=operation, bool_result=True, initializer=value)
        operation = token_argument(r"MakeBinaryOperationAction\([^,]+,\s*ExpressionType\.([A-Za-z]+)")
        if operation:
            return Binder(index, "binary", operation=operation, initializer=value)
        operation = token_argument(r"MakeUnaryOperationAction\([^,]+,\s*ExpressionType\.([A-Za-z]+)")
        if operation:
            return Binder(index, "unary", operation=operation, initializer=value)
        if "MakeConversionAction" in value:
            return Binder(index, "conversion", operation="bool", initializer=value)
        name = string_argument(r"MakeGetAction\([^,]+,\s*(\"(?:\\.|[^\"])*\")")
        if name is not None:
            return Binder(index, "get", name=name, initializer=value)
        name = string_argument(r"MakeSetAction\([^,]+,\s*(\"(?:\\.|[^\"])*\")")
        if name is not None:
            return Binder(index, "set", name=name, initializer=value)
        if "MakeGetIndexAction" in value:
            return Binder(index, "get_index", initializer=value)
        if "MakeSetIndexAction" in value:
            return Binder(index, "set_index", initializer=value)
        if "MakeDeleteIndexAction" in value:
            return Binder(index, "delete_index", initializer=value)
        if "MakeGetSliceBinder" in value:
            return Binder(index, "get_slice", initializer=value)
        if "MakeSetSliceBinder" in value:
            return Binder(index, "set_slice", initializer=value)
        match = re.search(r"MakeOperationAction\([^,]+,\s*(\d+)\)", value)
        if match:
            number = int(match.group(1))
            return Binder(
                index,
                "operation",
                operation=PYTHON_OPERATION_KINDS.get(number, "Operation%d" % number),
                initializer=value,
            )
        if "MakeInvokeAction" in value:
            return Binder(
                index,
                "invoke",
                call_arguments=tuple(self._parse_call_signature(value)),
                initializer=value,
            )
        return None

    @staticmethod
    def _parse_call_signature(value: str) -> list[tuple[str, str | None]]:
        simple = re.search(r"new CallSignature\((\d+)\)", value)
        if simple:
            return [("simple", None)] * int(simple.group(1))
        signature = re.search(r"new CallSignature\((.*)\)\)\s*\)?\s*\Z", value, re.S)
        if not signature:
            return []
        result: list[tuple[str, str | None]] = []
        for kind, raw_name in re.findall(
            r"new Argument\(ArgumentType\.([A-Za-z]+),\s*(null|\"(?:\\.|[^\"])*\")\)",
            signature.group(1),
        ):
            name = None if raw_name == "null" else decode_csharp_string(raw_name)
            result.append((kind.lower(), name))
        return result

    # ------------------------------------------------------------------
    # Expression inversion

    def _argument_nodes(self, invocation: Node) -> list[Node]:
        argument_list = next(
            (child for child in invocation.named_children if child.type == "argument_list"),
            None,
        )
        if argument_list is None:
            return []
        result = []
        for argument in argument_list.named_children:
            if argument.type == "argument" and argument.named_children:
                result.append(argument.named_children[-1])
            else:
                result.append(argument)
        return result

    def _global_expression(self, raw: str) -> str | None:
        canonical = ScopeContext.canonical(raw)
        matches = re.findall(
            r"(?:globalArrayFromContext\d*|Item\d{3})\[(\d+)\]\.(?:Current|Raw)Value",
            canonical,
        )
        if matches and canonical.endswith(("CurrentValue", "RawValue")):
            index = int(matches[-1])
            if 0 <= index < len(self.global_names):
                return self.global_names[index]
        return None

    @staticmethod
    def _callsite_index(raw: str) -> int | None:
        canonical = ScopeContext.canonical(raw)
        matches = re.findall(r"(?:strongBox\.Value|array|\.Value)\[(\d+)\]", canonical)
        return int(matches[-1]) if matches else None

    def expression(self, node: Node | None, context: ScopeContext) -> Expr:
        if node is None:
            return Expr("None", unresolved=True)
        raw = self.document.text(node)
        # ILSpy reuses generated identifiers in disjoint regions.  Resolve an
        # identifier at its lexical byte position before consulting flat
        # expression aliases retained for source-name allocation.
        if node.type == "identifier":
            version = context.identifier_at(raw, node.start_byte)
            if version is not None:
                return Expr(version)
        alias = context.lookup_alias(raw)
        if alias is not None:
            return Expr(alias)
        global_name = self._global_expression(raw)
        if global_name is not None:
            return Expr(global_name)
        canonical = ScopeContext.canonical(raw)
        constant_match = re.fullmatch(r"(?:strongBox\.Value|array|\(\(StrongBox<object\[\]>\).+?\)\.Value)\[(\d+)\]", canonical)
        if constant_match:
            index = int(constant_match.group(1))
            constant = self.constant_nodes.get(index)
            if constant is not None and constant is not node:
                return self.expression(constant, context)

        if context.tuple_slots:
            slot = self._generator_tuple_slot(raw)
            if slot is not None and slot in context.tuple_slots:
                return Expr(context.tuple_slots[slot])
            if slot is not None and slot in context.generator_temp_slots:
                return Expr(context.generator_temp_slots[slot])

        kind = node.type
        if kind in {"parenthesized_expression", "checked_expression"}:
            child = node.named_children[-1] if node.named_children else None
            return self.expression(child, context)
        if kind in {"cast_expression", "as_expression"}:
            value = node.child_by_field_name("value")
            if value is None and node.named_children:
                value = node.named_children[-1]
            return self.expression(value, context)
        if kind == "argument" and node.named_children:
            return self.expression(node.named_children[-1], context)
        if kind == "identifier":
            identifier = raw
            version = context.identifier_at(identifier, node.start_byte)
            if version is not None:
                return Expr(version)
            decoded = decode_identifier(identifier)
            if decoded in {"null", "default"}:
                return Expr("None")
            return Expr(decoded)
        if kind in {"null_literal", "default_literal", "default_expression"}:
            return Expr("None")
        if kind in {"true", "true_literal"} or kind == "boolean_literal" and raw == "true":
            return Expr("True")
        if kind in {"false", "false_literal"} or kind == "boolean_literal" and raw == "false":
            return Expr("False")
        if kind in {"string_literal", "character_literal"}:
            try:
                return Expr(python_repr(decode_csharp_string(raw)))
            except (ValueError, SyntaxError):
                return Expr(repr(raw.strip('"')))
        if kind in {"integer_literal", "real_literal"}:
            value = re.sub(r"(?i)(UL|LU|L|U|F|D|M)$", "", raw)
            return Expr(value)
        if kind == "predefined_type":
            return Expr(raw)
        if kind == "assignment_expression":
            # Assignment expressions occur inside ILSpy's call-site receiver
            # and light-exception temporary lowering.  Python 2 has no walrus;
            # the containing generated expression consumes the assigned value.
            right = node.child_by_field_name("right")
            if right is None and node.named_children:
                right = node.named_children[-1]
            value = self.expression(right, context)
            left = node.child_by_field_name("left")
            if left is None and node.named_children:
                left = node.named_children[0]
            if left is not None and left.type == "identifier":
                identifier = self.document.text(left)
                if not re.match(r"\s*\(CallSite<", self.document.text(right)):
                    context.identifier_aliases[identifier] = value.text
            elif (
                left is not None
                and context.scope is not None
                and context.scope.is_generator
            ):
                slot = self._generator_tuple_slot(self.document.text(left))
                if slot is not None and slot not in context.tuple_slots:
                    context.add_alias(self.document.text(left), value.text)
            return value
        if kind == "member_access_expression":
            return self._member_expression(node, context)
        if kind == "element_access_expression":
            return self._element_expression(node, context)
        if kind == "invocation_expression":
            return self._invocation_expression(node, context)
        if kind in {"array_creation_expression", "implicit_array_creation_expression"}:
            initializer = next(
                (child for child in node.named_children if child.type == "initializer_expression"),
                None,
            )
            values = [] if initializer is None else [
                self.expression(child, context).text for child in initializer.named_children
            ]
            return Expr("[%s]" % ", ".join(values))
        if kind == "initializer_expression":
            values = [self.expression(child, context).text for child in node.named_children]
            return Expr("[%s]" % ", ".join(values))
        if kind == "object_creation_expression":
            return self._object_creation(node, context)
        if kind == "binary_expression":
            left_node = node.child_by_field_name("left") or node.named_children[0]
            right_node = node.child_by_field_name("right") or node.named_children[-1]
            left = self.expression(left_node, context)
            right = self.expression(right_node, context)
            operator_raw = self.document.data[left_node.end_byte:right_node.start_byte].decode().strip()
            operator = CSHARP_BINARY_OPERATORS.get(operator_raw, operator_raw)
            precedence = {
                "or": 10, "and": 20,
                "==": 30, "!=": 30, "<": 30, "<=": 30, ">": 30, ">=": 30,
                "|": 40, "^": 45, "&": 50, "<<": 55, ">>": 55,
                "+": 60, "-": 60, "*": 70, "/": 70, "%": 70,
            }.get(operator, 30)
            return Expr(
                "%s %s %s" % (
                    left.parenthesized(precedence),
                    operator,
                    right.parenthesized(precedence + (1 if operator in {"-", "/"} else 0)),
                ),
                precedence,
            )
        if kind in {"prefix_unary_expression", "postfix_unary_expression"}:
            child = node.named_children[-1] if node.named_children else None
            operand = self.expression(child, context)
            prefix = raw[:raw.find(self.document.text(child))].strip() if child else ""
            operator = {"!": "not ", "~": "~", "-": "-", "+": "+"}.get(prefix, prefix)
            return Expr(operator + operand.parenthesized(80), 80)
        if kind == "conditional_expression":
            if (
                "PythonOps.IsUnicode" in raw
                and "PythonOps.GetUnicodeFuntion" in raw
            ):
                consequence_node = (
                    node.child_by_field_name("consequence")
                    or node.named_children[1]
                )
                return self.expression(consequence_node, context)
            short_circuit = self._short_circuit_expression(node, context)
            if short_circuit is not None:
                return short_circuit
            condition_node = node.child_by_field_name("condition") or node.named_children[0]
            consequence_node = node.child_by_field_name("consequence") or node.named_children[1]
            alternative_node = node.child_by_field_name("alternative") or node.named_children[2]
            condition = self.expression(condition_node, context)
            consequence = self.expression(consequence_node, context)
            alternative = self.expression(alternative_node, context)
            if condition.text.startswith("not "):
                positive = Expr(condition.text[4:], condition.precedence)
                if consequence.text == positive.text:
                    return Expr(
                        "%s and %s" % (
                            positive.parenthesized(20),
                            alternative.parenthesized(20),
                        ),
                        20,
                    )
                if alternative.text == positive.text:
                    return Expr(
                        "%s or %s" % (
                            positive.parenthesized(10),
                            consequence.parenthesized(10),
                        ),
                        10,
                    )
                condition = positive
                consequence, alternative = alternative, consequence
            if consequence.text == condition.text:
                return Expr(
                    "%s or %s" % (
                        condition.parenthesized(10),
                        alternative.parenthesized(10),
                    ),
                    10,
                )
            if alternative.text == condition.text:
                return Expr(
                    "%s and %s" % (
                        condition.parenthesized(20),
                        consequence.parenthesized(20),
                    ),
                    20,
                )
            return Expr(
                "%s if %s else %s" % (
                    consequence.parenthesized(6),
                    condition.parenthesized(6),
                    alternative.parenthesized(6),
                ),
                5,
            )
        if kind == "typeof_expression":
            type_node = node.named_children[-1] if node.named_children else None
            return Expr(self.document.text(type_node) if type_node else "object")
        if kind == "base_expression":
            return Expr("super")

        self.diagnostic(context, "expression", "%s: %s" % (kind, raw[:240]))
        return Expr("__ipy_unresolved__(%s)" % repr(raw), unresolved=True)

    def _member_expression(self, node: Node, context: ScopeContext) -> Expr:
        raw = self.document.text(node)
        if ScopeContext.canonical(raw) == "PythonOps.EmptyTuple":
            return Expr("()")
        alias = context.lookup_alias(raw)
        if alias is not None:
            return Expr(alias)
        global_name = self._global_expression(raw)
        if global_name is not None:
            return Expr(global_name)
        expression_node = node.child_by_field_name("expression")
        name_node = node.child_by_field_name("name")
        if expression_node is None and len(node.named_children) >= 2:
            expression_node, name_node = node.named_children[0], node.named_children[-1]
        left = self.expression(expression_node, context)
        name = decode_identifier(self.document.text(name_node))
        if left.text == "Uninitialized" and name == "Instance":
            return Expr("None")
        if left.text == "MissingParameter" and name == "Value":
            return Expr("")
        if name in {"CurrentValue", "RawValue"}:
            return left
        return Expr("%s.%s" % (left.parenthesized(90), name), 90)

    def _element_expression(self, node: Node, context: ScopeContext) -> Expr:
        raw = self.document.text(node)
        alias = context.lookup_alias(raw)
        if alias is not None:
            return Expr(alias)
        expression_node = node.child_by_field_name("expression")
        if expression_node is None:
            expression_node = node.named_children[0]
        base = self.expression(expression_node, context)
        arguments = [
            child for child in node.named_children
            if child is not expression_node and child.type not in {"bracketed_argument_list"}
        ]
        bracket = next(
            (child for child in node.named_children if child.type == "bracketed_argument_list"),
            None,
        )
        if bracket is not None:
            arguments = [
                child.named_children[-1] if child.type == "argument" else child
                for child in bracket.named_children
            ]
        indexes = [self.expression(child, context).text for child in arguments]
        return Expr("%s[%s]" % (base.parenthesized(90), ", ".join(indexes)), 90)

    def _object_creation(self, node: Node, context: ScopeContext) -> Expr:
        type_node = node.child_by_field_name("type")
        if type_node is None and node.named_children:
            type_node = node.named_children[0]
        type_name = self.document.text(type_node)
        args = self._argument_nodes(node)
        rendered = [self.expression(argument, context).text for argument in args]
        return Expr("%s(%s)" % (decode_identifier(type_name), ", ".join(rendered)), 90)

    def _short_circuit_expression(
        self,
        node: Node,
        context: ScopeContext,
    ) -> Expr | None:
        condition_node = node.child_by_field_name("condition") or node.named_children[0]
        consequence_node = node.child_by_field_name("consequence") or node.named_children[1]
        alternative_node = node.child_by_field_name("alternative") or node.named_children[2]
        condition_raw = self.document.text(condition_node).strip()
        while condition_raw.startswith("(") and condition_raw.endswith(")"):
            unwrapped = unwrap_single(condition_raw)
            if unwrapped == condition_raw:
                break
            condition_raw = unwrapped
        if not condition_raw.startswith("!"):
            return None
        candidates: list[tuple[int, str, Node]] = []
        for assignment in self.document.descendants(condition_node, "assignment_expression"):
            left = assignment.child_by_field_name("left") or assignment.named_children[0]
            right = assignment.child_by_field_name("right") or assignment.named_children[-1]
            left_raw = self.document.text(left).strip()
            right_raw = self.document.text(right)
            if left.type != "identifier":
                continue
            if re.match(r"\s*\(CallSite<", right_raw):
                continue
            candidates.append((assignment.end_byte - assignment.start_byte, left_raw, right))
        if not candidates:
            return None
        _, temporary, assigned_node = max(candidates)
        consequence_raw = ScopeContext.canonical(self.document.text(consequence_node))
        alternative_raw = ScopeContext.canonical(self.document.text(alternative_node))
        temporary_raw = ScopeContext.canonical(temporary)
        assigned = self.expression(assigned_node, context)
        context.aliases[temporary_raw] = assigned.text
        if consequence_raw == temporary_raw:
            other = self.expression(alternative_node, context)
            return Expr(
                "%s and %s" % (assigned.parenthesized(20), other.parenthesized(20)),
                20,
            )
        if alternative_raw == temporary_raw:
            other = self.expression(consequence_node, context)
            return Expr(
                "%s or %s" % (assigned.parenthesized(10), other.parenthesized(10)),
                10,
            )
        return None

    def _invocation_expression(self, node: Node, context: ScopeContext) -> Expr:
        function_node = node.child_by_field_name("function")
        if function_node is None and node.named_children:
            function_node = node.named_children[0]
        function_raw = self.document.text(function_node)
        args_nodes = self._argument_nodes(node)

        if function_raw.endswith(".Target"):
            receiver = function_node.child_by_field_name("expression") if function_node else None
            index = self._callsite_index(self.document.text(receiver))
            if index is not None and index in self.binders:
                return self._apply_binder(self.binders[index], args_nodes, context)
            self.diagnostic(context, "callsite", "binder not found: %s" % function_raw[:240])
            return Expr("__ipy_callsite_unresolved__()", unresolved=True)
        delegate_binder = context.delegate_binder_at(function_raw, node.start_byte)
        if delegate_binder is not None:
            return self._apply_binder(
                delegate_binder,
                args_nodes,
                context,
            )

        qualified = function_raw
        args = [self.expression(argument, context) for argument in args_nodes]
        if qualified.startswith("LightExceptions."):
            method = qualified.rsplit(".", 1)[-1]
            if method in {"CheckAndThrow", "GetLightException"} and args:
                return args[0]
            if method == "Throw" and args:
                if args[0].statement == "raise":
                    return Expr("None", statement="raise")
                return Expr(args[0].text, statement="raise %s" % args[0].text)
        if qualified.startswith("ScriptingRuntimeHelpers."):
            method = qualified.rsplit(".", 1)[-1]
            if method.endswith("ToObject") and args:
                return args[0]
        if qualified == "PythonOps.CheckUninitialized" and args:
            if len(args_nodes) > 1:
                name_raw = self.document.text(args_nodes[1])
                try:
                    name = decode_csharp_string(name_raw)
                    context.add_alias(self.document.text(args_nodes[0]), name)
                    return Expr(name)
                except ValueError:
                    pass
            return args[0]
        if qualified.startswith("PythonOps."):
            return self._pythonops_invocation(qualified.rsplit(".", 1)[-1], args_nodes, args, context)
        if qualified == "CompilerHelpers.CreateBigInteger":
            return self._big_integer(args_nodes, context)
        if qualified == "MathUtils.MakeImaginary" and args:
            value = args[0].text
            if value.endswith(".0"):
                value = value[:-2]
            return Expr(value + "j")
        if qualified in {"ExceptionHelpers.UpdateForRethrow"} and args:
            return args[0]

        function = self.expression(function_node, context)
        return Expr("%s(%s)" % (function.parenthesized(90), ", ".join(arg.text for arg in args)), 90)

    def _apply_binder(
        self,
        binder: Binder,
        nodes: list[Node],
        context: ScopeContext,
    ) -> Expr:
        # First delegate argument is the CallSite instance itself.
        operands_nodes = nodes[1:]
        operands = [self.expression(node, context) for node in operands_nodes]
        self.stats["binder_%s" % binder.kind] += 1

        if binder.kind == "get" and operands:
            target = operands[0]
            return Expr("%s.%s" % (target.parenthesized(90), binder.name), 90)
        if binder.kind == "set" and len(operands) >= 2:
            target, value = operands[0], operands[-1]
            text = "%s.%s = %s" % (target.parenthesized(90), binder.name, value.text)
            return Expr(value.text, statement=text)
        if binder.kind == "invoke" and len(operands) >= 2:
            # Invoke delegates serialize CodeContext immediately after CallSite.
            callable_expr = operands[1]
            call_values = operands[2:]
            signature = list(binder.call_arguments)
            if len(signature) != len(call_values):
                signature = [("simple", None)] * len(call_values)
            rendered = []
            for (argument_kind, name), value in zip(signature, call_values):
                if argument_kind == "named":
                    rendered.append("%s=%s" % (name, value.text))
                elif argument_kind == "list":
                    rendered.append("*%s" % value.parenthesized(80))
                elif argument_kind == "dictionary":
                    rendered.append("**%s" % value.parenthesized(80))
                else:
                    rendered.append(value.text)
            if (
                len(call_values) == 1
                and call_values[0].scope_ref is not None
                and not call_values[0].scope_ref.is_lambda
                and not call_values[0].scope_ref.is_comprehension
            ):
                decorated = call_values[0]
                return Expr(
                    decorated.scope_ref.name,
                    scope_ref=decorated.scope_ref,
                    defaults=list(decorated.defaults),
                    decorators=[callable_expr.text] + list(decorated.decorators),
                )
            return Expr("%s(%s)" % (callable_expr.parenthesized(90), ", ".join(rendered)), 90)
        if binder.kind == "conversion" and operands:
            return Expr(operands[0].text, operands[0].precedence)
        if binder.kind == "unary" and operands:
            operator = UNARY_OPERATORS.get(binder.operation or "", "")
            return Expr(operator + operands[0].parenthesized(80), 80)
        if binder.kind == "binary" and len(operands) >= 2:
            operator = EXPRESSION_OPERATORS.get(binder.operation or "", binder.operation or "?")
            if operator.endswith("=") and operator not in {"==", "!=", "<=", ">="}:
                # The call returns the updated value.  Assignment emission can
                # collapse ``x = InPlace(x, y)`` back to ``x += y``.
                text = "%s %s %s" % (operands[0].text, operator[:-1], operands[1].text)
                return Expr(text, 60, statement="%s %s %s" % (operands[0].text, operator, operands[1].text))
            precedence = 30 if operator in {"==", "!=", "<", "<=", ">", ">="} else (
                70 if operator in {"*", "/", "%"} else 60
            )
            if operator == "**":
                precedence = 75
            return Expr(
                "%s %s %s" % (
                    operands[0].parenthesized(precedence),
                    operator,
                    operands[1].parenthesized(precedence + (1 if operator in {"-", "/"} else 0)),
                ),
                precedence,
            )
        if binder.kind in {"get_index", "get_slice"} and operands:
            target = operands[0]
            values = [value.text for value in operands[1:]]
            if binder.kind == "get_slice":
                return Expr("%s[%s]" % (target.parenthesized(90), ":".join(values)), 90)
            index = ", ".join(values)
            return Expr("%s[%s]" % (target.parenthesized(90), index), 90)
        if binder.kind in {"set_index", "set_slice"} and len(operands) >= 3:
            target = operands[0]
            value = operands[-1]
            indexes = [item.text for item in operands[1:-1]]
            index = ":".join(indexes) if binder.kind == "set_slice" else ", ".join(indexes)
            lvalue = "%s[%s]" % (target.parenthesized(90), index)
            if value.statement and value.statement.startswith(lvalue + " "):
                statement = value.statement
            elif value.statement and len(operands) >= 3:
                # In-place operations often receive GetIndex(target, index) as
                # their left operand.  Preserve the compact augmented form.
                match = re.match(r".+?\s(\S+=)\s(.+)$", value.statement)
                statement = "%s %s %s" % (lvalue, match.group(1), match.group(2)) if match else "%s = %s" % (lvalue, value.text)
            else:
                statement = "%s = %s" % (lvalue, value.text)
            return Expr(value.text, statement=statement)
        if binder.kind == "delete_index" and len(operands) >= 2:
            lvalue = "%s[%s]" % (
                operands[0].parenthesized(90),
                ", ".join(value.text for value in operands[1:]),
            )
            return Expr("None", statement="del %s" % lvalue)
        if binder.kind == "operation":
            operation = binder.operation
            if operation == "Contains" and len(operands) >= 2:
                return Expr("%s in %s" % (operands[0].text, operands[1].text), 30)
            if operation == "GetEnumeratorForIteration" and operands:
                return Expr("iter(%s)" % operands[0].text, 90)
            if operation == "Length" and operands:
                return Expr("len(%s)" % operands[0].text, 90)
            if operation in {"AbsoluteValue", "Positive", "Negate", "OnesComplement", "Not", "IsFalse"} and operands:
                operators = {"AbsoluteValue": "abs", "Positive": "+", "Negate": "-", "OnesComplement": "~", "Not": "not ", "IsFalse": "not "}
                operator = operators[operation]
                return Expr("%s(%s)" % (operator, operands[0].text), 90) if operation == "AbsoluteValue" else Expr(operator + operands[0].parenthesized(80), 80)
            if operation in OPERATION_OPERATORS and len(operands) >= 2:
                operator = OPERATION_OPERATORS[operation]
                return Expr("%s %s %s" % (operands[0].text, operator, operands[1].text), 60)

        self.diagnostic(context, "binder", "%d %s %s" % (binder.index, binder.kind, binder.operation))
        return Expr("__ipy_binder_%d__(%s)" % (binder.index, ", ".join(item.text for item in operands)), unresolved=True)

    def _pythonops_invocation(
        self,
        method: str,
        nodes: list[Node],
        args: list[Expr],
        context: ScopeContext,
    ) -> Expr:
        if method in {
            "GetParentContextFromFunction", "GetGlobalContext",
            "GetGlobalArrayFromContext", "PushFrame", "CreateLocalContext",
            "GetClosureTupleFromFunction", "GetClosureTupleFromGenerator",
            "MakeClosureCell",
        }:
            return Expr("None")
        if method == "GetUnicodeFuntion":
            return Expr("unicode")
        if method == "IsUnicode":
            return Expr("True")
        if method.startswith("GetEnumeratorValues") and len(args) >= 2:
            return args[1]
        if method in {"MakeTuple", "MakeListNoCopy", "MakeList", "MakeSet"}:
            values = args
            if len(nodes) == 1 and nodes[0].type in {"array_creation_expression", "implicit_array_creation_expression"}:
                initializer = next((child for child in nodes[0].named_children if child.type == "initializer_expression"), None)
                values = [] if initializer is None else [self.expression(child, context) for child in initializer.named_children]
            content = ", ".join(value.text for value in values)
            if method == "MakeTuple":
                if len(values) == 1 and values[0].text.startswith("[") and values[0].text.endswith("]"):
                    inner = values[0].text[1:-1]
                    return Expr("(%s)" % inner)
                if len(values) == 1:
                    content += ","
                return Expr("(%s)" % content)
            if method == "MakeSet":
                return Expr("set([%s])" % content)
            return Expr("[%s]" % content)
        if method in {"MakeEmptyListFromCode"}:
            return Expr("[]")
        if method in {"MakeEmptyDict"}:
            return Expr("{}")
        if method == "MakeEmptySet":
            return Expr("set()")
        if method in {"MakeHomogeneousDictFromItems", "MakeDictFromItems"} and nodes:
            initializer = next((child for child in nodes[0].named_children if child.type == "initializer_expression"), None)
            values = [] if initializer is None else [self.expression(child, context) for child in initializer.named_children]
            # IronPython stores alternating value, key entries.
            pairs = ["%s: %s" % (values[i + 1].text, values[i].text) for i in range(0, len(values) - 1, 2)]
            return Expr("{%s}" % ", ".join(pairs))
        if method in {"MakeConstantDict", "MakeConstantDictStorage"}:
            return Expr("dict(%s)" % ", ".join(arg.text for arg in args), 90)
        if method == "Is" and len(args) >= 2:
            return Expr("%s is %s" % (args[0].text, args[1].text), 30)
        if method == "IsNot" and len(args) >= 2:
            return Expr("%s is not %s" % (args[0].text, args[1].text), 30)
        if method == "IsTrue" and args:
            return args[0]
        if method == "MakeException" and len(args) >= 2:
            return args[1]
        if method in {"MakeRethrownException", "MakeRethrowExceptionWorker"}:
            return Expr("None", statement="raise")
        if method == "RaiseAssertionError":
            if len(args) >= 2:
                return Expr(
                    "None", statement="assert False, %s" % args[1].text
                )
            return Expr("None", statement="assert False")
        if method == "LookupName" and len(nodes) >= 2:
            try:
                return Expr(decode_csharp_string(self.document.text(nodes[1])))
            except ValueError:
                pass
        if method == "SetName" and len(nodes) >= 3:
            try:
                name = decode_csharp_string(self.document.text(nodes[1]))
                return Expr(args[2].text, statement="%s = %s" % (name, args[2].text))
            except ValueError:
                pass
        if method == "MakeFunction" and len(nodes) >= 2:
            raw_code = self.document.text(nodes[1])
            match = re.search(r"(?:strongBox\.Value|\.Value|array)\[(\d+)\]", ScopeContext.canonical(raw_code))
            scope = self.scope_by_code_index.get(int(match.group(1))) if match else None
            defaults: list[str] = []
            if len(nodes) >= 4 and self.document.text(nodes[3]).strip() != "null":
                default_expr = self.expression(nodes[3], context)
                defaults = self._list_contents(default_expr.text)
            if scope is None:
                self.diagnostic(context, "function", "unmapped FunctionCode: %s" % raw_code)
                return Expr("__ipy_function__()", unresolved=True)
            if scope.is_lambda:
                body = self._lambda_body(scope)
                signature = self._signature(scope, defaults)
                return Expr("lambda %s: %s" % (signature, body), 1, scope_ref=scope, defaults=defaults)
            return Expr(scope.name, scope_ref=scope, defaults=defaults)
        if method == "MakeClass" and nodes:
            raw_code = self.document.text(nodes[0])
            match = re.search(r"(?:strongBox\.Value|\.Value|array)\[(\d+)\]", ScopeContext.canonical(raw_code))
            scope = self.scope_by_code_index.get(int(match.group(1))) if match else None
            bases: list[str] = []
            if len(nodes) >= 5:
                bases = self._list_contents(self.expression(nodes[4], context).text)
            if scope is None:
                self.diagnostic(context, "class", "unmapped FunctionCode: %s" % raw_code)
                return Expr("__ipy_class__()", unresolved=True)
            return Expr(scope.name, scope_ref=scope, defaults=bases)
        if method == "MakeGeneratorExpression" and len(args) >= 2:
            scope = args[0].scope_ref if args else None
            if scope is not None and scope.is_comprehension:
                recovered = self._recover_generator_expression(
                    scope, args[1], context
                )
                if recovered is not None:
                    return recovered
            self.diagnostic(context, "generator_expression", "state expression was not invertible")
            return Expr("(__ipy_unresolved_generator_value__ for _item in %s)" % args[1].text, unresolved=True)
        if method == "ImportTop" and len(nodes) >= 2:
            try:
                return Expr(decode_csharp_string(self.document.text(nodes[1])))
            except ValueError:
                pass
        if method == "ImportBottom" and len(nodes) >= 2:
            try:
                return Expr(decode_csharp_string(self.document.text(nodes[1])))
            except ValueError:
                pass
        if method == "ImportFrom" and len(nodes) >= 3:
            try:
                return Expr(decode_csharp_string(self.document.text(nodes[2])))
            except ValueError:
                pass
        if method == "FormatString" and len(args) >= 2:
            values = args[1:] if len(args) >= 3 else args
            return Expr("%s %% %s" % (values[0].text, values[1].text), 60)
        if method == "ListAddForComprehension" and len(args) >= 2:
            return Expr("None", statement="%s.append(%s)" % (args[0].text, args[1].text))
        if method == "DictAddForComprehension" and len(args) >= 3:
            return Expr("None", statement="%s[%s] = %s" % (args[0].text, args[1].text, args[2].text))
        if method == "SetAddForComprehension" and len(args) >= 2:
            return Expr("None", statement="%s.add(%s)" % (args[0].text, args[1].text))
        if method == "MakeBytes" and args:
            initializer = next(
                (
                    child
                    for node in nodes
                    for child in node.named_children
                    if child.type == "initializer_expression"
                ),
                None,
            )
            if initializer is not None:
                values = []
                for child in initializer.named_children:
                    value = self.expression(child, context).text
                    if re.fullmatch(r"\d+", value):
                        values.append(int(value))
                if values:
                    return Expr(repr(bytes(values)))
            return args[-1]
        if method == "EmptyTuple":
            return Expr("()")
        if method in {"Print", "PrintComma", "PrintNewline"}:
            # PythonOps print helpers always take CodeContext first.  In a
            # generator it is held in an opaque MutableTuple slot, so its
            # reconstructed spelling cannot be used to identify it.
            values = args[1:] if args else []
            suffix = "," if method == "PrintComma" else ""
            return Expr("None", statement="print %s%s" % (", ".join(value.text for value in values), suffix))
        if method == "GeneratorCheckThrowableAndReturnSendValue":
            # Internal marker consumed by generator state-machine recovery.
            return Expr("__ipy_generator_send_value__")
        if "Exception" in method:
            # These are handled structurally by exception/generator recovery.
            return Expr("__ipy_%s__(%s)" % (method, ", ".join(arg.text for arg in args)), unresolved=True)

        rendered = ", ".join(arg.text for arg in args)
        self.diagnostic(context, "pythonops", "%s(%s)" % (method, rendered[:300]))
        return Expr("__ipy_%s__(%s)" % (method, rendered), 90, unresolved=True)

    @staticmethod
    def _list_contents(text: str) -> list[str]:
        text = text.strip()
        if text == "None":
            return []
        if text.startswith("[") and text.endswith("]"):
            return split_balanced(text[1:-1]) if text[1:-1].strip() else []
        return [text]

    def _big_integer(self, nodes: list[Node], context: ScopeContext) -> Expr:
        if len(nodes) == 1:
            return self.expression(nodes[0], context)
        raw_sign = self.document.text(nodes[0])
        negative = raw_sign.rstrip().endswith("true")
        raw_data = self.document.text(nodes[1])
        values = [int(value) for value in re.findall(r"\b\d+\b", raw_data)]
        # Discard the array length when it precedes an initializer.
        length = re.search(r"new byte\[(\d+)\]", raw_data)
        if length and values and values[0] == int(length.group(1)):
            values = values[1:]
        integer = int.from_bytes(bytes(values), "little", signed=False)
        if negative:
            integer = -integer
        return Expr("%dL" % integer)

    def _lambda_body(self, scope: Scope) -> str:
        nodes = self._scope_method_nodes(scope)
        if not nodes:
            return "__ipy_unresolved_lambda__()"
        context = ScopeContext(self, scope)
        self._prepare_context(nodes[0], context)
        returns = list(self.document.descendants(nodes[0], "return_statement"))
        if returns:
            value = returns[-1].child_by_field_name("value")
            if value is None and returns[-1].named_children:
                value = returns[-1].named_children[-1]
            return self.expression(value, context).text
        return "None"

    def _recover_generator_expression(
        self,
        scope: Scope,
        iterable: Expr,
        outer_context: ScopeContext,
    ) -> Expr | None:
        nodes = self._scope_method_nodes(scope)
        if not nodes:
            return None
        node = nodes[0]
        context = ScopeContext(self, scope)
        self._prepare_context(node, context)

        assignments = list(self.document.descendants(node, "assignment_expression"))
        prospective_yields = []
        for assignment in assignments:
            left = assignment.child_by_field_name("left") or assignment.named_children[0]
            if re.search(
                r"\.Item001$", ScopeContext.canonical(self.document.text(left))
            ):
                prospective_yields.append(assignment)
        first_yield_byte = min(
            (item.start_byte for item in prospective_yields),
            default=node.end_byte,
        )

        source_slots = set(context.tuple_slots)
        temporary_assignments = []
        for assignment in assignments:
            left = assignment.child_by_field_name("left") or assignment.named_children[0]
            right = assignment.child_by_field_name("right") or assignment.named_children[-1]
            match = re.search(r"\.Item(\d{3})$", ScopeContext.canonical(self.document.text(left)))
            if match is None:
                continue
            slot = int(match.group(1))
            if (
                slot in source_slots
                or slot in {0, 1, 2, 4, 5, 6}
            ):
                continue
            temporary_assignments.append((assignment, left, right))

        dataflow: list[tuple[int, str, Node, Node | None]] = []
        for assignment, left, right in temporary_assignments:
            dataflow.append((assignment.end_byte, "tuple", left, right))
        for assignment in assignments:
            left = assignment.child_by_field_name("left") or assignment.named_children[0]
            right = assignment.child_by_field_name("right") or assignment.named_children[-1]
            if left.type == "identifier" and not re.fullmatch(
                r"num\d*", self.document.text(left)
            ):
                dataflow.append((assignment.end_byte, "identifier", left, right))
        for declarator in self.document.descendants(node, "variable_declarator"):
            if len(declarator.named_children) < 2:
                continue
            name_node = declarator.child_by_field_name("name") or declarator.named_children[0]
            initializer = declarator.named_children[-1]
            raw = self.document.text(initializer)
            if raw.endswith(".Target") or any(marker in raw for marker in (
                "GetGlobalContext", "GetGlobalArrayFromContext", "PushFrame",
            )):
                continue
            dataflow.append((declarator.end_byte, "identifier", name_node, initializer))

        # Replay completion order.  Repetition closes aliases where ILSpy nests
        # assignments inside a variable initializer (the inner assignment ends
        # first, followed by the declarator itself).
        for _ in range(3):
            for position, kind, left, right in sorted(dataflow, key=lambda item: item[0]):
                value = self.expression(right, context)
                if kind == "tuple":
                    context.add_alias(self.document.text(left), value.text)
                else:
                    context.add_identifier_version(
                        self.document.text(left), position, value.text
                    )

        yields: list[tuple[Node, Expr]] = []
        seen_yields: set[int] = set()
        for assignment in assignments:
            left = assignment.child_by_field_name("left") or assignment.named_children[0]
            if not re.search(
                r"\.Item001$", ScopeContext.canonical(self.document.text(left))
            ):
                continue
            if assignment.start_byte in seen_yields:
                continue
            seen_yields.add(assignment.start_byte)
            right = assignment.child_by_field_name("right") or assignment.named_children[-1]
            yields.append((assignment, self.expression(right, context)))
        if not yields:
            return None

        def contained(item: Node, container: Node | None) -> bool:
            return bool(
                container is not None
                and container.start_byte <= item.start_byte
                and item.end_byte <= container.end_byte
            )

        def values_in(container: Node | None) -> list[tuple[Node, Expr]]:
            return [item for item in yields if contained(item[0], container)]

        def branch_value(container: Node) -> Expr | None:
            local = values_in(container)
            if len(local) == 1:
                return local[0][1]
            candidates = []
            for conditional in self.document.descendants(container, "if_statement"):
                consequence = conditional.child_by_field_name("consequence")
                alternative = conditional.child_by_field_name("alternative")
                left_values = values_in(consequence)
                right_values = values_in(alternative)
                if left_values and right_values:
                    candidates.append(conditional)
            for conditional in sorted(
                candidates,
                key=lambda item: item.end_byte - item.start_byte,
                reverse=True,
            ):
                consequence = conditional.child_by_field_name("consequence")
                alternative = conditional.child_by_field_name("alternative")
                left_value = branch_value(consequence)
                right_value = branch_value(alternative)
                if left_value is None or right_value is None:
                    continue
                condition = self.expression(
                    conditional.child_by_field_name("condition"), context
                )
                if left_value.text == condition.text:
                    return Expr(
                        "%s or %s" % (
                            condition.parenthesized(10),
                            right_value.parenthesized(10),
                        ),
                        10,
                    )
                if right_value.text == condition.text:
                    return Expr(
                        "%s and %s" % (
                            condition.parenthesized(20),
                            left_value.parenthesized(20),
                        ),
                        20,
                    )
                return Expr(
                    "%s if %s else %s" % (
                        left_value.parenthesized(6),
                        condition.parenthesized(6),
                        right_value.parenthesized(6),
                    ),
                    5,
                )
            return None

        value = yields[0][1] if len(yields) == 1 else branch_value(node)
        if value is None:
            return None

        target_names = [
            name for name in scope.variable_names[1:]
            if not name.startswith("<")
        ]
        if not target_names:
            target = "_item"
        elif len(target_names) == 1:
            target = target_names[0]
        else:
            target = "(%s)" % ", ".join(target_names)

        loop_condition_slots = set()
        for assignment in assignments:
            left = assignment.child_by_field_name("left") or assignment.named_children[0]
            right = assignment.child_by_field_name("right") or assignment.named_children[-1]
            if ".Key.MoveNext" in self.document.text(right):
                loop_condition_slots.add(ScopeContext.canonical(self.document.text(left)))

        filters: list[str] = []
        first_yield = yields[0][0]
        ancestor = first_yield.parent
        common_conditionals: list[Node] = []
        while ancestor is not None and ancestor is not node:
            if ancestor.type == "if_statement" and all(
                contained(item[0], ancestor) for item in yields
            ):
                consequence = ancestor.child_by_field_name("consequence")
                alternative = ancestor.child_by_field_name("alternative")
                if (
                    len(values_in(consequence)) == len(yields)
                    and not values_in(alternative)
                ):
                    common_conditionals.append(ancestor)
            ancestor = ancestor.parent
        for conditional in reversed(common_conditionals):
            condition_node = conditional.child_by_field_name("condition")
            raw = ScopeContext.canonical(self.document.text(condition_node))
            if (
                raw in loop_condition_slots
                or "Item000" in raw
                or re.search(r"\bnum\d*\b", raw)
                or "LightExceptions" in raw
            ):
                continue
            condition = self.expression(condition_node, context)
            if condition.text not in filters:
                filters.append(condition.text)

        suffix = "".join(" if %s" % item for item in filters)
        self.stats["generator_expressions_recovered"] += 1
        return Expr(
            "(%s for %s in %s%s)" % (
                value.text, target, iterable.text, suffix,
            ),
            100,
        )

    # ------------------------------------------------------------------
    # Scope and statement recovery

    def _scope_method_nodes(self, scope: Scope) -> list[Node]:
        inline = getattr(self, "inline_scope_nodes", {}).get(id(scope))
        if inline is not None:
            return [inline]
        if not scope.target_method:
            return []
        nodes = list(self.document.methods.get(scope.target_method, []))
        if scope.is_generator and len(nodes) > 1:
            nodes.sort(
                key=lambda node: (
                    "MutableTuple tupleArg" not in self.document.text(node.child_by_field_name("parameters")),
                    node.start_byte,
                )
            )
        return nodes

    def _prepare_context(self, node: Node, context: ScopeContext) -> None:
        # Stack-trace calls expose the compiler's source-line local explicitly.
        for invocation in self.document.descendants(node, "invocation_expression"):
            raw = self.document.text(invocation)
            if raw.startswith("PythonOps.UpdateStackTrace"):
                args = self._argument_nodes(invocation)
                if args:
                    candidate = self.document.text(args[-1]).strip()
                    if (
                        re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", candidate)
                        or context.scope is not None
                        and context.scope.is_generator
                        and re.fullmatch(
                            r"[A-Za-z_][A-Za-z0-9_]*\.Item\d{3}", candidate
                        )
                    ):
                        context.line_identifiers.add(candidate)
            if raw.startswith("PythonOps.CheckUninitialized"):
                args = self._argument_nodes(invocation)
                if len(args) >= 2:
                    try:
                        name = decode_csharp_string(self.document.text(args[1]))
                    except ValueError:
                        continue
                    context.add_alias(self.document.text(args[0]), name)

        for declarator in self.document.descendants(node, "variable_declarator"):
            if len(declarator.named_children) < 2:
                continue
            identifier = self.document.text(
                declarator.child_by_field_name("name") or declarator.named_children[0]
            )
            initializer = declarator.named_children[-1]
            raw = self.document.text(initializer)
            if raw.endswith(".Target"):
                index = self._callsite_index(raw)
                if index is not None and index in self.binders:
                    owner = declarator.parent
                    while owner is not None and owner.type not in {
                        "block", "switch_section", "method_declaration",
                        "anonymous_method_expression",
                    }:
                        owner = owner.parent
                    end_byte = owner.end_byte if owner is not None else node.end_byte
                    context.add_delegate_binder(
                        identifier,
                        declarator.start_byte,
                        end_byte,
                        self.binders[index],
                    )

            global_name = self._global_expression(raw)
            if global_name is None:
                slot_match = re.fullmatch(
                    r"(?:globalArrayFromContext\d*|Item\d{3})\[(\d+)\]",
                    ScopeContext.canonical(raw),
                )
                if slot_match is not None:
                    slot_index = int(slot_match.group(1))
                    if 0 <= slot_index < len(self.global_names):
                        global_name = self.global_names[slot_index]
            if global_name is not None:
                context.add_alias(identifier, global_name)
                context.add_identifier_version(
                    identifier,
                    declarator.start_byte,
                    global_name,
                )

        # ILSpy hoists delegate locals when a light-exception region has more
        # than one control-flow path, then assigns ``targetN = callSite.Target``
        # inside the path that uses it.  These assignments carry the same
        # binder identity as initialized delegate declarations above.
        for assignment in self.document.descendants(node, "assignment_expression"):
            left = assignment.child_by_field_name("left") or assignment.named_children[0]
            right = assignment.child_by_field_name("right") or assignment.named_children[-1]
            if left.type != "identifier":
                continue
            raw = self.document.text(right)
            if not raw.endswith(".Target"):
                continue
            index = self._callsite_index(raw)
            if index is None or index not in self.binders:
                continue
            owner = assignment.parent
            while owner is not None and owner.type not in {
                "block", "switch_section", "method_declaration",
                "anonymous_method_expression",
            }:
                owner = owner.parent
            end_byte = owner.end_byte if owner is not None else node.end_byte
            context.add_delegate_binder(
                self.document.text(left),
                assignment.start_byte,
                end_byte,
                self.binders[index],
            )

        scope = context.scope
        if scope is None:
            return

        parameter_owner = (
            node.parent
            if node.type == "block" and node.parent
            and node.parent.type == "anonymous_method_expression"
            else node
        )
        parameter_list = (
            parameter_owner.child_by_field_name("parameters")
            if parameter_owner is not None else None
        )
        if parameter_list is not None and scope.argument_names:
            actual_parameters: list[str] = []
            for parameter in parameter_list.named_children:
                if parameter.type != "parameter":
                    continue
                name_node = parameter.child_by_field_name("name")
                if name_node is not None:
                    actual_parameters.append(self.document.text(name_node))
            if len(actual_parameters) >= len(scope.argument_names):
                for actual, serialized in zip(
                    actual_parameters[-len(scope.argument_names):],
                    scope.argument_names,
                ):
                    context.identifier_aliases[actual] = serialized

        # Closure cells are allocated in serialized variable order.
        cell_names = list(scope.variable_names if scope.is_class else scope.cell_variables)
        cell_index = 0
        for declarator in self.document.descendants(node, "variable_declarator"):
            raw = self.document.text(declarator)
            if "PythonOps.MakeClosureCell" not in raw:
                continue
            if cell_index >= len(cell_names):
                break
            identifier = self.document.text(declarator.child_by_field_name("name"))
            if not identifier and declarator.named_children:
                identifier = self.document.text(declarator.named_children[0])
            name = cell_names[cell_index]
            context.add_alias(identifier, name)
            context.add_alias(identifier + ".Value", name)
            cell_index += 1

        # Free/cell tuples use Item000, Item001, ... in serialized order.
        closure_names = list(scope.free_variables) + [
            name for name in scope.cell_variables if name not in scope.free_variables
        ]
        for declarator in self.document.descendants(node, "variable_declarator"):
            raw = self.document.text(declarator)
            if "GetClosureTupleFrom" not in raw:
                continue
            identifier = self.document.text(declarator.child_by_field_name("name"))
            if not identifier and declarator.named_children:
                identifier = self.document.text(declarator.named_children[0])
            for index, name in enumerate(closure_names):
                context.add_alias("%s.Item%03d" % (identifier, index), name)
                context.add_alias("%s.Item%03d.Value" % (identifier, index), name)

        if scope.is_generator:
            argument_count = len(scope.argument_names)
            tuple_types: list[str] = []
            for statement in self.document.descendants(
                node, "local_declaration_statement"
            ):
                for identifier, _, type_name in self._variable_parts(statement):
                    if (
                        identifier == "mutableTuple"
                        and type_name.startswith("MutableTuple<")
                        and type_name.endswith(">")
                    ):
                        tuple_types = [
                            item.strip()
                            for item in split_balanced(
                                type_name[len("MutableTuple<"):-1]
                            )
                        ]
                        break
                if tuple_types:
                    break
            for index, name in enumerate(scope.argument_names):
                context.tuple_slots[3 + index] = name

            local_start = 3 + argument_count + 3
            if "PythonGlobal[]" in tuple_types:
                globals_slot = tuple_types.index("PythonGlobal[]")
                local_start = globals_slot + 1
                cell_slot = local_start
                for cell_name in scope.cell_variables:
                    if (
                        cell_slot < len(tuple_types)
                        and tuple_types[cell_slot] == "ClosureCell"
                    ):
                        raw = "mutableTuple.Item%03d" % cell_slot
                        context.add_alias(raw, cell_name)
                        context.add_alias(raw + ".Value", cell_name)
                        cell_slot += 1
                local_start = cell_slot

            non_arguments = scope.variable_names[argument_count:]
            for offset, name in enumerate(non_arguments):
                context.tuple_slots[local_start + offset] = name

    def _semantic_block(self, node: Node, module: bool = False) -> Node:
        if node.type == "block":
            root = node
        else:
            root = node.child_by_field_name("body") or node
        marker = "PythonOps.ModuleStarted" if module else "PythonOps.PushFrame"
        candidates: list[Node] = []
        for block in self.document.descendants(root, "block"):
            direct = "\n".join(self.document.text(child) for child in block.named_children[:8])
            if marker in direct:
                candidates.append(block)
        if candidates:
            return min(candidates, key=lambda block: block.end_byte - block.start_byte)
        return root

    def _signature(self, scope: Scope, defaults: Sequence[str] = ()) -> str:
        names = list(scope.argument_names)
        keyword = "KeywordDictionary" in scope.flags
        varargs = "ArgumentList" in scope.flags
        keyword_name = names.pop() if keyword and names else None
        varargs_name = names.pop() if varargs and names else None
        rendered = list(names)
        if defaults:
            count = min(len(defaults), len(rendered))
            start = len(rendered) - count
            rendered[start:] = [
                "%s=%s" % (name, value)
                for name, value in zip(rendered[start:], list(defaults)[-count:])
            ]
        if varargs_name:
            rendered.append("*" + varargs_name)
        elif keyword_name:
            # Python 2 requires a bare-star only in Python 3, so there is no
            # separator before a sole **kwargs parameter.
            pass
        if keyword_name:
            rendered.append("**" + keyword_name)
        return ", ".join(rendered)

    def _emit_scope(
        self,
        scope: Scope,
        writer: PythonWriter,
        defaults: Sequence[str] = (),
        decorators: Sequence[str] = (),
        bases: Sequence[str] = (),
    ) -> None:
        for decorator in decorators:
            writer.write("@" + decorator)
        if scope.is_class:
            suffix = "(%s)" % ", ".join(bases) if bases else ""
            header = "class %s%s:" % (scope.name, suffix)
        else:
            header = "def %s(%s):" % (scope.name, self._signature(scope, defaults))
        before = len(writer.lines)
        with writer.block(header):
            if scope.documentation is not None:
                writer.write(repr(scope.documentation))
            nodes = self._scope_method_nodes(scope)
            if not nodes:
                writer.write("pass  # unresolved: cached delegate body was not mapped")
                self.diagnostic(ScopeContext(self, scope), "scope", "delegate body not mapped")
            elif scope.is_generator:
                self._emit_generator(scope, nodes[0], writer)
            else:
                context = ScopeContext(self, scope)
                self._prepare_context(nodes[0], context)
                body = self._semantic_block(nodes[0])
                initial = len(writer.lines)
                self._emit_block(body, context, writer, skip_scaffold_prefix=True)
                if len(writer.lines) == initial:
                    writer.write("pass")
        if len(writer.lines) == before + 1:
            writer.write("    pass")

    def _emit_generator(self, scope: Scope, node: Node, writer: PythonWriter) -> None:
        context = ScopeContext(self, scope)
        self._prepare_context(node, context)
        self._prepare_generator_reverse_aliases(node, context)
        self._prepare_generator_comprehensions(node, context)
        context.generator_emitted_nodes = set()
        context.generator_yield_count = 0
        body = node.child_by_field_name("body") or node
        self._emit_generator_nodes(body.named_children, context, writer)
        if context.generator_yield_count == 0:
            self.diagnostic(context, "generator", "no state-machine yield was recovered")
            writer.write("if False:")
            writer.indent += 1
            writer.write("yield None")
            writer.indent -= 1

    def _prepare_generator_comprehensions(
        self,
        node: Node,
        context: ScopeContext,
    ) -> None:
        """Name transient comprehension containers used by generator bodies."""
        operations = {
            "ListAddForComprehension": ("_listcomp", "[]"),
            "DictAddForComprehension": ("_dictcomp", "{}"),
            "SetAddForComprehension": ("_setcomp", "set()"),
        }
        for invocation in self.document.descendants(node, "invocation_expression"):
            function = invocation.child_by_field_name("function") or invocation.named_children[0]
            method = self.document.text(function).rsplit(".", 1)[-1]
            if method not in operations:
                continue
            arguments = self._argument_nodes(invocation)
            if not arguments:
                continue
            raw = ScopeContext.canonical(self.document.text(arguments[0]))
            if not re.fullmatch(r"mutableTuple\d*\.Item\d{3}", raw):
                continue
            if raw not in context.generator_comprehensions:
                prefix, literal = operations[method]
                context.generator_comprehensions[raw] = (
                    context.allocate_synthetic(prefix), literal,
                )

    def _prepare_generator_reverse_aliases(
        self,
        node: Node,
        context: ScopeContext,
    ) -> None:
        """Propagate serialized source slots backward through compiler temps."""
        source_names = set(context.tuple_slots.values())
        storage_assignment_counts = Counter(
            slot
            for assignment in self.document.descendants(
                node, "assignment_expression"
            )
            for slot in [self._generator_tuple_slot(self.document.text(
                assignment.child_by_field_name("left")
                or assignment.named_children[0]
            ))]
            if slot is not None
        )
        for _ in range(5):
            changed = False
            for assignment in reversed(
                list(self.document.descendants(node, "assignment_expression"))
            ):
                left = assignment.child_by_field_name("left") or assignment.named_children[0]
                right = assignment.child_by_field_name("right") or assignment.named_children[-1]
                left_raw = self.document.text(left)
                slot = self._generator_tuple_slot(left_raw)
                target = (
                    context.tuple_slots.get(slot)
                    if slot is not None else context.lookup_alias(left_raw)
                    or context.identifier_aliases.get(left_raw)
                )
                if target not in source_names:
                    continue
                right_raw = self.document.text(right)
                if right.type == "identifier":
                    if context.identifier_aliases.get(right_raw) != target:
                        context.identifier_aliases[right_raw] = target
                        changed = True
                elif (
                    right.type in {"member_access_expression", "element_access_expression"}
                    and self._is_generator_storage_reference(right_raw)
                    and storage_assignment_counts[
                        self._generator_tuple_slot(right_raw)
                    ] <= 1
                ):
                    if context.lookup_alias(right_raw) != target:
                        context.add_alias(right_raw, target)
                        changed = True
            for declarator in reversed(
                list(self.document.descendants(node, "variable_declarator"))
            ):
                if len(declarator.named_children) < 2:
                    continue
                name_node = declarator.child_by_field_name("name") or declarator.named_children[0]
                identifier = self.document.text(name_node)
                target = context.identifier_aliases.get(identifier)
                if target not in source_names:
                    continue
                initializer = declarator.named_children[-1]
                raw = self.document.text(initializer)
                if initializer.type == "identifier":
                    if context.identifier_aliases.get(raw) != target:
                        context.identifier_aliases[raw] = target
                        changed = True
                elif (
                    initializer.type in {"member_access_expression", "element_access_expression"}
                    and self._is_generator_storage_reference(raw)
                    and storage_assignment_counts[
                        self._generator_tuple_slot(raw)
                    ] <= 1
                ):
                    if context.lookup_alias(raw) != target:
                        context.add_alias(raw, target)
                        changed = True
            if not changed:
                break

    def _generator_tuple_slot(self, raw: str) -> int | None:
        match = re.fullmatch(
            r"mutableTuple\d*\.Item(\d{3})",
            ScopeContext.canonical(raw),
        )
        return int(match.group(1)) if match else None

    @staticmethod
    def _is_generator_storage_reference(raw: str) -> bool:
        """Return whether *raw* is a state tuple slot or its unpack array.

        A serialized global is spelled ``mutableTuple.Item006[n].CurrentValue``
        in generator delegates.  Treating that as a state alias conflates a
        Python global (for example ``True``) with the local receiving it.
        """
        return re.fullmatch(
            r"mutableTuple\d*\.Item\d{3}(?:\[\d+\])?",
            ScopeContext.canonical(raw),
        ) is not None

    def _generator_yield_assignment(self, node: Node) -> Node | None:
        candidates = []
        if node.type == "assignment_expression":
            candidates.append(node)
        candidates.extend(self.document.descendants(node, "assignment_expression"))
        for assignment in candidates:
            left = assignment.child_by_field_name("left") or assignment.named_children[0]
            if self._generator_tuple_slot(self.document.text(left)) == 1:
                return assignment
        return None

    def _generator_loop_target(self, raw: str, context: ScopeContext) -> str:
        slot = self._generator_tuple_slot(raw)
        if slot is not None and slot in context.tuple_slots:
            return context.tuple_slots[slot]
        alias = context.lookup_alias(raw) or context.identifier_aliases.get(raw)
        if alias is not None:
            return alias
        return context.allocate_name(raw)

    def _generator_states_in(
        self,
        nodes: Sequence[Node],
        context: ScopeContext,
    ) -> list[tuple[int, int | None]]:
        states: list[tuple[int, int | None]] = []
        assignments = sorted(
            (
                assignment
                for node in nodes
                for assignment in self.document.descendants(
                    node, "assignment_expression"
                )
            ),
            key=lambda item: item.start_byte,
        )
        yields = [
            item for item in assignments
            if self._generator_tuple_slot(self.document.text(
                item.child_by_field_name("left") or item.named_children[0]
            )) == 1
        ]
        for yielded in yields:
            source_line = None
            for node in nodes:
                if node.start_byte >= yielded.start_byte:
                    break
                for statement in self.document.descendants(
                    node, "expression_statement"
                ):
                    if statement.start_byte >= yielded.start_byte:
                        break
                    value = self._line_value(statement, context)
                    if value is not None:
                        source_line = value
            candidates = []
            for assignment in assignments:
                if assignment.start_byte <= yielded.start_byte:
                    continue
                left = assignment.child_by_field_name("left") or assignment.named_children[0]
                right = assignment.child_by_field_name("right") or assignment.named_children[-1]
                if self._generator_tuple_slot(self.document.text(left)) != 0:
                    continue
                raw = self.document.text(right).strip()
                if re.fullmatch(r"[1-9]\d*", raw):
                    candidates.append((assignment.start_byte, int(raw)))
            if candidates:
                state = min(candidates)[1]
                if not any(item[0] == state for item in states):
                    states.append((state, source_line))
        return states

    def _generator_resume_nodes(
        self,
        statement: Node,
        state: int,
        enumerator: str,
        context: ScopeContext | None = None,
    ) -> tuple[list[Node], list[Node]]:
        candidates: list[Node] = []
        for section in self.document.descendants(statement, "switch_section"):
            match = re.match(
                r"\s*case\s+(\d+)\s*:", self.document.text(section)
            )
            if (
                match is not None
                and int(match.group(1)) == state
                and "GeneratorCheckThrowableAndReturnSendValue" in self.document.text(section)
            ):
                candidates.append(section)
        if not candidates:
            return [], []
        section = min(candidates, key=lambda item: item.end_byte - item.start_byte)
        if context is not None:
            context.generator_consumed_sections.add(section.start_byte)
        container = next(
            (child for child in section.named_children if child.type == "block"),
            section,
        )
        children = list(container.named_children)
        repeated_index = next(
            (
                index for index, child in enumerate(children)
                if enumerator + ".Key.MoveNext" in self.document.text(child)
            ),
            None,
        )
        if repeated_index is None:
            return children, []
        return [], children[repeated_index + 1:]

    def _emit_generator_continuation(
        self,
        nodes: Sequence[Node],
        statement: Node,
        context: ScopeContext,
        writer: PythonWriter,
    ) -> None:
        if not nodes:
            return
        enumerators_before = set(context.loop_enumerators)
        self._emit_generator_nodes(nodes, context, writer)
        for nested_enumerator in (
            key for key in context.loop_enumerators
            if key not in enumerators_before
        ):
            nested_iterable = context.loop_enumerators[nested_enumerator]
            if self._emit_for_try(
                statement,
                nested_enumerator,
                nested_iterable,
                context,
                writer,
                generator=True,
            ) or self._emit_generator_for_try(
                statement,
                context,
                writer,
                only_enumerator=nested_enumerator,
            ):
                continue

    def _emit_generator_for_try(
        self,
        statement: Node,
        context: ScopeContext,
        writer: PythonWriter,
        only_enumerator: str | None = None,
    ) -> bool:
        body = statement.child_by_field_name("body")
        if body is None:
            return False
        for enumerator, iterable in list(context.loop_enumerators.items()):
            if only_enumerator is not None and enumerator != only_enumerator:
                continue
            canonical_enumerator = ScopeContext.canonical(enumerator)
            if canonical_enumerator in context.generator_consumed_enumerators:
                continue
            move_assignment: tuple[Node, Node, Node] | None = None
            for candidate in self.document.descendants(body, "expression_statement"):
                assignment = self._assignment_nodes(candidate)
                if assignment is None:
                    continue
                left, right = assignment
                if enumerator + ".Key.MoveNext" in self.document.text(right):
                    move_assignment = (candidate, left, right)
                    break
            if move_assignment is None:
                continue
            move_statement, flag_node, _ = move_assignment
            flag_raw = self.document.text(flag_node)
            loop_if = next(
                (
                    candidate for candidate in self.document.descendants(body, "if_statement")
                    if candidate.start_byte > move_statement.start_byte
                    and flag_raw in self.document.text(
                        candidate.child_by_field_name("condition")
                    )
                    and enumerator + ".Key.Current" in self.document.text(candidate)
                ),
                None,
            )
            if loop_if is not None:
                consequence = loop_if.child_by_field_name("consequence")
                if consequence is None:
                    continue
                children = (
                    list(consequence.named_children)
                    if consequence.type == "block" else [consequence]
                )
            else:
                # ILSpy also emits ``moved = MoveNext(); if (!moved) break;``
                # followed by the current-value assignment as a sibling.
                guard = next(
                    (
                        candidate
                        for candidate in self.document.descendants(body, "if_statement")
                        if candidate.start_byte > move_statement.start_byte
                        and flag_raw in self.document.text(
                            candidate.child_by_field_name("condition")
                        )
                        and enumerator + ".Key.Current" not in self.document.text(candidate)
                        and any(
                            child.type in {"break_statement", "goto_statement"}
                            for child in self.document.descendants(
                                candidate.child_by_field_name("consequence") or candidate,
                                "break_statement",
                            )
                        )
                    ),
                    None,
                )
                # ``descendants`` above is kind-specific; handle goto-only
                # guards independently.
                if guard is None:
                    guard = next(
                        (
                            candidate
                            for candidate in self.document.descendants(body, "if_statement")
                            if candidate.start_byte > move_statement.start_byte
                            and flag_raw in self.document.text(
                                candidate.child_by_field_name("condition")
                            )
                            and enumerator + ".Key.Current" not in self.document.text(candidate)
                            and list(self.document.descendants(candidate, "goto_statement"))
                        ),
                        None,
                    )
                if guard is None or guard.parent is None:
                    continue
                children = list(guard.parent.named_children)
                try:
                    guard_position = children.index(guard)
                except ValueError:
                    continue
                children = children[guard_position + 1:]
            current_index = None
            current_left: Node | None = None
            current_raw = ""
            for position, child in enumerate(children):
                assignment = self._assignment_nodes(child)
                if assignment is None:
                    continue
                left, right = assignment
                if enumerator + ".Key.Current" in self.document.text(right):
                    current_index = position
                    current_left = left
                    current_raw = self.document.text(left)
                    break
            if current_index is None or current_left is None:
                # ILSpy can express the current value as a local declaration.
                for position, child in enumerate(children):
                    parts = self._variable_parts(child)
                    if len(parts) != 1 or parts[0][1] is None:
                        continue
                    if enumerator + ".Key.Current" in self.document.text(parts[0][1]):
                        current_index = position
                        current_raw = parts[0][0]
                        break
            if current_index is None:
                continue
            target = self._generator_loop_target(current_raw, context)
            target = self._valid_loop_target(target, current_raw, context)
            context.add_alias(current_raw, target)
            semantic = children[current_index + 1:]
            context.generator_consumed_enumerators.add(canonical_enumerator)
            resume_states = self._generator_states_in(semantic, context)
            after_continuations: list[list[Node]] = []
            with writer.block("for %s in %s:" % (target, iterable.text)):
                before = len(writer.lines)
                enumerators_before = set(context.loop_enumerators)
                context.generator_loop_depth += 1
                try:
                    self._emit_generator_nodes(semantic, context, writer)
                    # A suspended nested ``for`` is split by ILSpy: its iterator
                    # setup remains in the outer MoveNext consequence, while its
                    # MoveNext/current block is a later sibling in this same try.
                    # Once setup registers the iterator, recover that continuation
                    # recursively inside the outer Python loop.
                    for nested_enumerator in (
                        key for key in context.loop_enumerators
                        if key not in enumerators_before
                    ):
                        nested_iterable = context.loop_enumerators[nested_enumerator]
                        if self._emit_for_try(
                            statement,
                            nested_enumerator,
                            nested_iterable,
                            context,
                            writer,
                            generator=True,
                        ) or self._emit_generator_for_try(
                            statement,
                            context,
                            writer,
                            only_enumerator=nested_enumerator,
                        ):
                            break
                    for resume_state, yield_line in resume_states:
                        resume_key = (
                            ScopeContext.canonical(enumerator), resume_state
                        )
                        if resume_key in context.generator_resume_processed:
                            continue
                        inside_nodes, after_nodes = self._generator_resume_nodes(
                            statement, resume_state, enumerator, context
                        )
                        if not inside_nodes and not after_nodes:
                            continue
                        if after_nodes and yield_line is not None:
                            continuation_lines = sorted(
                                (
                                    (node.start_byte, line)
                                    for node in after_nodes
                                    for line in self._source_lines_in(node, context)
                                ),
                                key=lambda item: item[0],
                            )
                            if (
                                continuation_lines
                                and continuation_lines[0][1] <= yield_line
                            ):
                                after_nodes = []
                        context.generator_resume_processed.add(resume_key)
                        self._emit_generator_continuation(
                            inside_nodes, statement, context, writer
                        )
                        if after_nodes:
                            after_continuations.append(after_nodes)
                finally:
                    context.generator_loop_depth -= 1
                if len(writer.lines) == before:
                    writer.write("pass")
            for continuation in after_continuations:
                self._emit_generator_continuation(
                    continuation, statement, context, writer
                )
            context.semantic_statements += 1
            return True
        return False

    def _emit_generator_if(
        self,
        statement: Node,
        context: ScopeContext,
        writer: PythonWriter,
    ) -> None:
        condition_node = statement.child_by_field_name("condition")
        consequence = statement.child_by_field_name("consequence")
        alternative = statement.child_by_field_name("alternative")
        raw = self.document.text(condition_node)
        if re.search(r"\bnum\d*\b", raw) or "Item000" in raw:
            # ``!=`` branches are the initial execution path; equality branches
            # only restore a suspended state already represented by ``yield``.
            selected = consequence if "!=" in raw else alternative
            if selected is not None:
                nested = selected.named_children if selected.type == "block" else [selected]
                self._emit_generator_nodes(nested, context, writer)
            return
        condition = self.expression(condition_node, context)
        is_loop = self._generator_if_is_loop(statement)
        keyword = "while" if is_loop else "if"
        branch_loop_recovered = False
        implicit_terminal_else = False
        yields_before_branch = context.generator_yield_count
        with writer.block("%s %s:" % (keyword, condition.parenthesized(6))):
            before = len(writer.lines)
            enumerators_before = set(context.loop_enumerators)
            nested = consequence.named_children if consequence and consequence.type == "block" else ([consequence] if consequence else [])
            self._emit_generator_nodes(nested, context, writer)
            for nested_enumerator in (
                key for key in context.loop_enumerators
                if key not in enumerators_before
            ):
                owner = statement.parent
                while owner is not None and owner.type != "try_statement":
                    owner = owner.parent
                if owner is None:
                    break
                nested_iterable = context.loop_enumerators[nested_enumerator]
                if self._emit_for_try(
                    owner,
                    nested_enumerator,
                    nested_iterable,
                    context,
                    writer,
                    generator=True,
                ) or self._emit_generator_for_try(
                    owner,
                    context,
                    writer,
                    only_enumerator=nested_enumerator,
                ):
                    branch_loop_recovered = True
                    break
            if is_loop:
                self._emit_generator_nodes(
                    self._generator_loop_update_nodes(statement),
                    context,
                    writer,
                )
            if len(writer.lines) == before:
                consequence_raw = self.document.text(consequence) if consequence else ""
                if re.search(r"\.Item000\s*=\s*0\b", consequence_raw):
                    writer.write("return")
                    context.semantic_statements += 1
                else:
                    writer.write("pass")
        if alternative is not None:
            if alternative.type == "if_statement":
                temp = PythonWriter()
                self._emit_generator_if(alternative, context, temp)
                if temp.lines and temp.lines[0].startswith("if "):
                    writer.write("el" + temp.lines[0])
                    for line in temp.lines[1:]:
                        writer.write(line)
            else:
                with writer.block("else:"):
                    before = len(writer.lines)
                    nested = alternative.named_children if alternative.type == "block" else [alternative]
                    self._emit_generator_nodes(nested, context, writer)
                    if len(writer.lines) == before:
                        writer.write("pass")
        elif (
            (branch_loop_recovered or context.generator_yield_count > yields_before_branch)
            and context.generator_loop_depth == 0
        ):
            siblings = list(statement.parent.named_children) if statement.parent else []
            try:
                position = siblings.index(statement)
            except ValueError:
                position = -1
            following = siblings[position + 1] if 0 <= position < len(siblings) - 1 else None
            if (
                following is not None
                and following.type == "goto_statement"
                and re.search(r"\bgoto\s+end_IL_", self.document.text(following))
            ):
                with writer.block("else:"):
                    writer.write("return")
                implicit_terminal_else = True
        if (
            branch_loop_recovered
            and not implicit_terminal_else
            and alternative is None
            and consequence is not None
            and list(self.document.descendants(consequence, "goto_statement"))
            and statement.parent is not None
        ):
            siblings = list(statement.parent.named_children)
            try:
                position = siblings.index(statement)
            except ValueError:
                position = -1
            trailing = siblings[position + 1:] if position >= 0 else []
            yield_position = next(
                (
                    index for index, child in enumerate(trailing)
                    if self._generator_yield_assignment(child) is not None
                ),
                None,
            )
            if yield_position is not None:
                end = yield_position + 1
                while end < len(trailing):
                    child = trailing[end]
                    end += 1
                    if child.type in {"goto_statement", "break_statement"}:
                        break
                    assignment = self._assignment_nodes(child)
                    if assignment is not None and self._generator_tuple_slot(
                        self.document.text(assignment[0])
                    ) == 0:
                        break
                else_nodes = trailing[:end]
                context.generator_emitted_nodes.update(
                    child.start_byte for child in else_nodes
                )
                with writer.block("else:"):
                    before = len(writer.lines)
                    # Allow this explicit rendering despite the consumed marks.
                    for child in else_nodes:
                        context.generator_emitted_nodes.discard(child.start_byte)
                    self._emit_generator_nodes(else_nodes, context, writer)
                    context.generator_emitted_nodes.update(
                        child.start_byte for child in else_nodes
                    )
                    if len(writer.lines) == before:
                        writer.write("pass")

    def _generator_if_is_loop(self, statement: Node) -> bool:
        """Recognize a state-resume switch that jumps back to an ``if`` test."""
        states: set[int] = set()
        for assignment in self.document.descendants(statement, "assignment_expression"):
            left = assignment.child_by_field_name("left") or assignment.named_children[0]
            right = assignment.child_by_field_name("right") or assignment.named_children[-1]
            if not re.search(
                r"\.Item000$", ScopeContext.canonical(self.document.text(left))
            ):
                continue
            raw_state = self.document.text(right).strip()
            if re.fullmatch(r"[1-9]\d*", raw_state):
                states.add(int(raw_state))
        if not states or statement.parent is None or statement.parent.type != "block":
            return False
        siblings = list(statement.parent.named_children)
        try:
            position = siblings.index(statement)
        except ValueError:
            return False
        for sibling in reversed(siblings[:position]):
            if sibling.type == "if_statement":
                condition = self.document.text(
                    sibling.child_by_field_name("condition")
                )
                alternative = sibling.child_by_field_name("alternative")
                match = re.search(r"\bnum\d*\s*!=\s*(\d+)\b", condition)
                if (
                    match is not None
                    and int(match.group(1)) in states
                    and alternative is not None
                ):
                    self.stats["generator_loops_recovered"] += 1
                    return True
            if sibling.type not in {
                "if_statement", "local_declaration_statement",
                "expression_statement", "switch_statement",
            }:
                break
        for sibling in reversed(siblings[:position]):
            if sibling.type not in {"switch_statement", "local_declaration_statement", "expression_statement"}:
                break
            if sibling.type != "switch_statement":
                continue
            for section in self.document.descendants(sibling, "switch_section"):
                match = re.match(
                    r"\s*case\s+(\d+)\s*:", self.document.text(section)
                )
                labels = {int(match.group(1))} if match is not None else set()
                if not labels.intersection(states):
                    continue
                if not list(self.document.descendants(section, "goto_statement")):
                    self.stats["generator_loops_recovered"] += 1
                    return True
            break
        return False

    def _generator_loop_update_nodes(self, statement: Node) -> list[Node]:
        states = {
            int(self.document.text(right).strip())
            for assignment in self.document.descendants(
                statement, "assignment_expression"
            )
            for left in [assignment.child_by_field_name("left") or assignment.named_children[0]]
            for right in [assignment.child_by_field_name("right") or assignment.named_children[-1]]
            if self._generator_tuple_slot(self.document.text(left)) == 0
            and re.fullmatch(r"[1-9]\d*", self.document.text(right).strip())
        }
        if not states or statement.parent is None:
            return []
        siblings = list(statement.parent.named_children)
        try:
            position = siblings.index(statement)
        except ValueError:
            return []
        for sibling in reversed(siblings[:position]):
            if sibling.type != "if_statement":
                continue
            condition = self.document.text(
                sibling.child_by_field_name("condition")
            )
            match = re.search(r"\bnum\d*\s*!=\s*(\d+)\b", condition)
            alternative = sibling.child_by_field_name("alternative")
            if (
                match is not None
                and int(match.group(1)) in states
                and alternative is not None
            ):
                return (
                    list(alternative.named_children)
                    if alternative.type == "block" else [alternative]
                )
        return []

    def _emit_generator_nodes(
        self,
        nodes: Sequence[Node],
        context: ScopeContext,
        writer: PythonWriter,
    ) -> None:
        for statement in nodes:
            if (
                statement is None
                or statement.start_byte in context.generator_emitted_nodes
                or statement.start_byte in context.skip_statement_bytes
                or statement.start_byte in context.generator_consumed_sections
            ):
                continue
            if statement.type == "break_statement":
                parent_raw = self.document.text(statement.parent) if statement.parent else ""
                if (
                    context.generator_loop_depth > 0
                    and not re.search(r"\.Item000\s*=", parent_raw)
                ):
                    writer.write("break")
                    context.semantic_statements += 1
                continue
            if statement.type == "continue_statement":
                if context.generator_loop_depth > 0:
                    writer.write("continue")
                    context.semantic_statements += 1
                continue
            if statement.type in {
                "case_switch_label", "default_switch_label", "goto_statement",
                "empty_statement", "finally_clause",
                "catch_clause",
            }:
                continue
            if statement.type in {"block", "switch_body", "switch_section"}:
                self._emit_generator_nodes(statement.named_children, context, writer)
                continue
            if statement.type == "switch_statement":
                switch_body = next(
                    (child for child in statement.named_children if child.type == "switch_body"),
                    None,
                )
                if switch_body is not None:
                    self._emit_generator_nodes(switch_body.named_children, context, writer)
                continue
            if statement.type == "try_statement":
                if self._python_user_try(statement):
                    if self._recover_python_try(statement, context, writer):
                        context.generator_emitted_nodes.add(statement.start_byte)
                        continue
                regular_loop = False
                for enumerator, iterable in list(context.loop_enumerators.items()):
                    if self._emit_for_try(
                        statement, enumerator, iterable, context, writer,
                        generator=True,
                    ):
                        regular_loop = True
                        break
                if regular_loop:
                    context.generator_emitted_nodes.add(statement.start_byte)
                    continue
                if self._emit_generator_for_try(statement, context, writer):
                    context.generator_emitted_nodes.add(statement.start_byte)
                    continue
                body = statement.child_by_field_name("body")
                if body is not None:
                    self._emit_generator_nodes(body.named_children, context, writer)
                continue
            if statement.type == "local_declaration_statement":
                yield_assignment = self._generator_yield_assignment(statement)
                if yield_assignment is not None:
                    right = yield_assignment.child_by_field_name("right") or yield_assignment.named_children[-1]
                    value = self.expression(right, context)
                    writer.write("yield %s" % value.text)
                    context.generator_yield_count += 1
                    context.semantic_statements += 1
                    continue
                for identifier, initializer, type_name in self._variable_parts(statement):
                    if initializer is None:
                        continue
                    raw = self.document.text(initializer)
                    if type_name.startswith((
                        "CallSite<", "Func<", "CodeContext", "PythonGlobal",
                        "StrongBox<", "MutableTuple<", "List<FunctionStack>",
                        "Exception",
                    )) or self._is_scaffold_value(raw):
                        continue
                    value = self.expression(initializer, context)
                    context.identifier_aliases[identifier] = value.text
                continue
            if statement.type == "expression_statement":
                line = self._line_value(statement, context)
                if line is not None:
                    context.current_line = line
                    continue
                yield_assignment = self._generator_yield_assignment(statement)
                if yield_assignment is not None:
                    right = yield_assignment.child_by_field_name("right") or yield_assignment.named_children[-1]
                    value = self.expression(right, context)
                    writer.write("yield %s" % value.text)
                    context.generator_yield_count += 1
                    context.semantic_statements += 1
                    context.generator_emitted_nodes.add(statement.start_byte)
                    continue
                assignment = self._assignment_nodes(statement)
                if assignment is not None:
                    left, right = assignment
                    left_raw = self.document.text(left)
                    right_raw = self.document.text(right)
                    if (
                        right_raw.endswith(".Target")
                        and self._callsite_index(right_raw) is not None
                    ):
                        continue
                    if re.fullmatch(r"num\d*", left_raw):
                        continue
                    if right_raw.strip() == "Uninitialized.Instance":
                        continue
                    value = self.expression(right, context)
                    if value.text.startswith("iter(") and value.text.endswith(")"):
                        context.loop_enumerators[left_raw] = Expr(value.text[5:-1])
                        context.add_alias(left_raw, left_raw)
                        continue
                    slot = self._generator_tuple_slot(left_raw)
                    if slot is not None and value.text == "__ipy_generator_send_value__":
                        target = context.tuple_slots.get(slot)
                        if target is None:
                            candidate = context.lookup_alias(left_raw)
                            if candidate in set(context.tuple_slots.values()):
                                target = candidate
                    else:
                        target = None
                    if target is not None:
                        prefix = "    " * writer.indent + "yield "
                        for line_index in range(len(writer.lines) - 1, -1, -1):
                            if writer.lines[line_index].startswith(prefix):
                                writer.lines[line_index] = (
                                    "    " * writer.indent
                                    + target
                                    + " = "
                                    + writer.lines[line_index].lstrip()
                                )
                                break
                        context.add_alias(left_raw, target)
                        continue
                    if slot is not None and slot not in context.tuple_slots:
                        existing = context.lookup_alias(left_raw)
                        source_names = set(context.tuple_slots.values())
                        comprehension = context.generator_comprehensions.get(
                            ScopeContext.canonical(left_raw)
                        )
                        if comprehension is not None and value.text == comprehension[1]:
                            synthetic_name, literal = comprehension
                            name = existing if existing in source_names else synthetic_name
                            context.add_alias(left_raw, name)
                            writer.write("%s = %s" % (name, literal))
                            context.semantic_statements += 1
                            continue
                        if "PythonOps.GetEnumeratorValues" in right_raw:
                            invocation = next(
                                (
                                    item for item in self.document.descendants(right, "invocation_expression")
                                    if self.document.text(
                                        item.child_by_field_name("function") or item.named_children[0]
                                    ).startswith("PythonOps.GetEnumeratorValues")
                                ),
                                None,
                            )
                            if invocation is not None:
                                arguments = self._argument_nodes(invocation)
                                count = (
                                    int(self.document.text(arguments[2]))
                                    if len(arguments) >= 3
                                    and re.fullmatch(r"\d+", self.document.text(arguments[2]).strip())
                                    else 0
                                )
                                targets = [
                                    context.lookup_alias("%s[%d]" % (left_raw, item))
                                    for item in range(count)
                                ]
                                if count and all(targets):
                                    unpacked = self.expression(arguments[1], context)
                                    writer.write("%s = %s" % (
                                        ", ".join(targets), unpacked.text,
                                    ))
                                    context.semantic_statements += 1
                                    continue
                        if existing in source_names:
                            if existing != value.text:
                                writer.write("%s = %s" % (existing, value.text))
                                context.semantic_statements += 1
                            continue
                        context.generator_temp_slots[slot] = value.text
                        context.add_alias(left_raw, value.text)
                        continue
                    if left.type == "identifier" and left_raw not in context.identifier_aliases:
                        context.identifier_aliases[left_raw] = value.text
                        continue
                    left_value = self._lvalue(left, context, allocate=False)
                    if self._emit_child_expression(value, context, writer):
                        continue
                    if left_value == value.text:
                        continue
                    self._emit_expression_statement(statement, context, writer)
                    continue
                if "GeneratorCheckThrowableAndReturnSendValue" in self.document.text(statement):
                    continue
                self._emit_expression_statement(statement, context, writer)
                continue
            if statement.type == "if_statement":
                self._emit_generator_if(statement, context, writer)
                continue
            if statement.type in {"while_statement", "for_statement"}:
                condition_node = statement.child_by_field_name("condition")
                body = statement.child_by_field_name("body")
                condition = self.expression(condition_node, context) if condition_node else Expr("True")
                if ".Key.MoveNext" in self.document.text(statement):
                    continue
                with writer.block("while %s:" % condition.parenthesized(6)):
                    before = len(writer.lines)
                    nested = body.named_children if body and body.type == "block" else ([body] if body else [])
                    self._emit_generator_nodes(nested, context, writer)
                    if len(writer.lines) == before:
                        writer.write("pass")
                continue
            if statement.type == "throw_statement":
                self._emit_throw(statement, context, writer)
                continue
            if statement.type == "return_statement":
                continue
            if statement.type == "labeled_statement":
                # IL labels are state-machine merge/dispatch points.  Loops and
                # yields nested below them are recovered from their enclosing
                # try/switch before this sequential fallback is reached.
                raw = self.document.text(statement)
                if any(
                    enumerator + ".Key.MoveNext" in ScopeContext.canonical(raw)
                    for enumerator in context.generator_consumed_enumerators
                ):
                    continue
                if ".Key.MoveNext" in raw or self._generator_yield_assignment(statement):
                    nested = (
                        statement.named_children[-1]
                        if statement.named_children else None
                    )
                    if nested is not None:
                        self._emit_generator_nodes([nested], context, writer)
                continue
            # Generated wrapper nodes (unsafe blocks and similar) are safe to
            # descend when they merely contain the semantic state machine.
            if statement.named_children:
                self._emit_generator_nodes(statement.named_children, context, writer)

    def _emit_child_expression(
        self,
        expression: Expr,
        context: ScopeContext,
        writer: PythonWriter,
    ) -> bool:
        scope = expression.scope_ref
        if scope is None or scope.is_lambda or scope.is_comprehension:
            return False
        marker = id(scope)
        if marker in context.emitted_children:
            return True
        context.emitted_children.add(marker)
        bases = expression.defaults if scope.is_class else ()
        defaults = () if scope.is_class else expression.defaults
        self._emit_scope(
            scope,
            writer,
            defaults=defaults,
            decorators=expression.decorators,
            bases=bases,
        )
        return True

    def _emit_block(
        self,
        block: Node,
        context: ScopeContext,
        writer: PythonWriter,
        skip_scaffold_prefix: bool = False,
        children: Sequence[Node] | None = None,
    ) -> None:
        statements = list(children if children is not None else block.named_children)
        index = 0
        while index < len(statements):
            statement = statements[index]
            if statement.start_byte in context.skip_statement_bytes:
                index += 1
                continue
            unpacked = self._emit_unpack_sequence(statements, index, context, writer)
            if unpacked:
                index += unpacked
                continue
            if statement.type == "local_declaration_statement":
                loop = self._loop_declaration(statement, context)
                if loop is not None and index + 1 < len(statements):
                    context.loop_enumerators[loop[0]] = loop[1]
                    if statements[index + 1].type == "try_statement" and self._emit_for_try(
                        statements[index + 1], loop[0], loop[1], context, writer
                    ):
                        index += 2
                        continue
                self._emit_local_declaration(statement, context, writer, skip_scaffold_prefix)
            elif statement.type == "expression_statement":
                loop = self._loop_assignment(statement, context)
                if loop is not None and index + 1 < len(statements):
                    context.loop_enumerators[loop[0]] = loop[1]
                    if statements[index + 1].type == "try_statement" and self._emit_for_try(
                        statements[index + 1], loop[0], loop[1], context, writer
                    ):
                        index += 2
                        continue
                self._emit_expression_statement(statement, context, writer)
            elif statement.type == "return_statement":
                self._emit_return(statement, context, writer)
            elif statement.type == "throw_statement":
                self._emit_throw(statement, context, writer)
            elif statement.type == "if_statement":
                condition = statement.child_by_field_name("condition")
                if "LightExceptions.IsLightException" in self.document.text(condition):
                    self._emit_light_nodes([statement], context, writer)
                else:
                    self._emit_if(statement, context, writer)
            elif statement.type == "while_statement":
                self._emit_while(statement, context, writer)
            elif statement.type == "for_statement":
                self._emit_csharp_for(statement, context, writer)
            elif statement.type == "try_statement":
                recovered_user_try = self._python_user_try(statement)
                if not self._emit_try(statement, context, writer):
                    self.diagnostic(context, "try", self.document.text(statement)[:300])
                elif recovered_user_try and index + 1 < len(statements):
                    # In CanSetSysExcInfo functions the direct CLR try/catch is
                    # followed by label-based light-exception continuations.
                    # They remain part of the Python source stream and must be
                    # decoded as data flow, not emitted as ordinary C# nodes.
                    remainder = statements[index + 1:]
                    if "LightExceptions" in "\n".join(
                        self.document.text(item) for item in remainder
                    ):
                        self._emit_light_nodes(remainder, context, writer)
                        return
            elif statement.type == "break_statement":
                writer.write("break")
                context.semantic_statements += 1
            elif statement.type == "continue_statement":
                writer.write("continue")
                context.semantic_statements += 1
            elif statement.type == "empty_statement":
                pass
            elif statement.type == "labeled_statement":
                # Compiler merge labels carry temporary propagation, never a
                # Python label (Python 2 has no such statement).
                pass
            elif statement.type in {"goto_statement", "switch_statement", "lock_statement"}:
                self.diagnostic(context, "control_flow", self.document.text(statement)[:300])
            else:
                self.diagnostic(context, "statement", "%s: %s" % (statement.type, self.document.text(statement)[:260]))
            index += 1

    def _emit_unpack_sequence(
        self,
        statements: Sequence[Node],
        index: int,
        context: ScopeContext,
        writer: PythonWriter,
    ) -> int:
        """Collapse ``SequenceExpression`` tuple-unpack temporaries."""
        first_parts = self._variable_parts(statements[index])
        if len(first_parts) != 1 or first_parts[0][1] is None:
            return 0

        rhs_identifier, rhs_node, _ = first_parts[0]
        unpack_index = index + 1
        unpack_parts = (
            self._variable_parts(statements[unpack_index])
            if unpack_index < len(statements) else []
        )

        explicit_rhs_temp = True
        if not (
            len(unpack_parts) == 1
            and unpack_parts[0][1] is not None
            and "PythonOps.GetEnumeratorValues" in self.document.text(unpack_parts[0][1])
        ):
            if "PythonOps.GetEnumeratorValues" not in self.document.text(rhs_node):
                return 0
            explicit_rhs_temp = False
            unpack_index = index
            unpack_parts = first_parts

        array_identifier, unpack_node, _ = unpack_parts[0]
        invocation = next(
            (
                item for item in self.document.descendants(unpack_node, "invocation_expression")
                if self.document.text(
                    item.child_by_field_name("function") or item.named_children[0]
                ).startswith("PythonOps.GetEnumeratorValues")
            ),
            None,
        )
        if invocation is None:
            return 0
        arguments = self._argument_nodes(invocation)
        if len(arguments) < 3:
            return 0
        count_match = re.fullmatch(r"\s*(\d+)\s*", self.document.text(arguments[2]))
        if count_match is None:
            return 0
        expected = int(count_match.group(1))
        if expected < 1:
            return 0

        targets: list[str] = []
        cursor = unpack_index + 1
        for slot in range(expected):
            if cursor >= len(statements):
                return 0
            candidate = statements[cursor]
            target_node: Node | None = None
            target_identifier: str | None = None
            value_node: Node | None = None
            parts = self._variable_parts(candidate)
            if len(parts) == 1 and parts[0][1] is not None:
                target_identifier, value_node, _ = parts[0]
            else:
                assignment = self._assignment_nodes(candidate)
                if assignment is not None:
                    target_node, value_node = assignment
            if value_node is None:
                return 0
            value_raw = ScopeContext.canonical(self.document.text(value_node))
            expected_access = ScopeContext.canonical(
                "%s[%d]" % (array_identifier, slot)
            )
            if expected_access not in value_raw:
                return 0
            if target_identifier is not None:
                target = context.allocate_name(target_identifier)
                target = self._valid_assignment_target(
                    target, target_identifier, context
                )
                context.add_alias(target_identifier, target)
            elif target_node is not None:
                target = self._lvalue(target_node, context)
                target = self._valid_assignment_target(
                    target, self.document.text(target_node), context
                )
            else:
                return 0
            targets.append(target)
            context.add_alias("%s[%d]" % (array_identifier, slot), target)
            cursor += 1

        if explicit_rhs_temp:
            rhs = self.expression(rhs_node, context)
            context.identifier_aliases[rhs_identifier] = rhs.text
        else:
            rhs = self.expression(arguments[1], context)
        context.identifier_aliases[array_identifier] = array_identifier
        writer.write("%s = %s" % (", ".join(targets), rhs.text))
        context.semantic_statements += 1
        return cursor - index

    def _variable_parts(self, statement: Node) -> list[tuple[str, Node | None, str]]:
        result: list[tuple[str, Node | None, str]] = []
        declaration = next(
            (child for child in statement.named_children if child.type == "variable_declaration"),
            None,
        )
        if declaration is None:
            return result
        type_node = declaration.child_by_field_name("type") or declaration.named_children[0]
        type_name = self.document.text(type_node)
        for declarator in declaration.named_children:
            if declarator.type != "variable_declarator":
                continue
            name_node = declarator.child_by_field_name("name") or declarator.named_children[0]
            initializer = declarator.named_children[-1] if len(declarator.named_children) > 1 else None
            result.append((self.document.text(name_node), initializer, type_name))
        return result

    def _is_scaffold_value(self, raw: str) -> bool:
        markers = (
            "GetGlobalContext", "GetParentContextFromFunction", "GetGlobalArrayFromContext",
            "PushFrame", "CreateLocalContext", "MakeClosureCell", "GetClosureTupleFrom",
            "P_0.Locals", "Uninitialized.Instance", "default(", "SaveCurrentException",
        )
        return any(marker in raw for marker in markers)

    def _emit_local_declaration(
        self,
        statement: Node,
        context: ScopeContext,
        writer: PythonWriter,
        skip_scaffold_prefix: bool,
    ) -> None:
        for identifier, initializer, type_name in self._variable_parts(statement):
            if initializer is None:
                continue
            raw = self.document.text(initializer)
            if raw.strip() == "MissingParameter.Value":
                context.identifier_aliases[identifier] = ""
                continue
            if "PythonOps.ImportWithNames" in raw:
                import_info = self._import_with_names_info(initializer, context)
                if import_info is not None:
                    context.import_modules[identifier] = import_info
                continue
            if self._is_scaffold_value(raw):
                if "Uninitialized.Instance" in raw:
                    context.uninitialized.add(identifier)
                continue
            if type_name.startswith(("CallSite<", "Func<", "CodeContext", "PythonGlobal", "StrongBox<", "ClosureCell", "MutableTuple<", "List<FunctionStack>", "Exception")):
                continue
            if type_name in {"List", "PythonDictionary", "SetCollection"} and any(
                marker in raw for marker in ("MakeList()", "MakeEmptyDict()", "MakeEmptySet()")
            ):
                context.identifier_aliases[identifier] = decode_identifier(identifier)
                value = self.expression(initializer, context)
                writer.write("%s = %s" % (decode_identifier(identifier), value.text))
                context.semantic_statements += 1
                continue
            value = self.expression(initializer, context)
            if value.statement and value.text == "None":
                if self._is_python_assignment_statement(value.statement):
                    writer.write(value.statement)
                    context.semantic_statements += 1
                else:
                    self.stats["invalid_statements_elided"] += 1
                continue
            preferred = context.lookup_alias(identifier)
            name = context.allocate_name(identifier, preferred)
            name = self._valid_assignment_target(name, identifier, context)
            if self._emit_child_expression(value, context, writer):
                continue
            writer.write("%s = %s" % (name, value.text))
            context.semantic_statements += 1

    def _assignment_nodes(self, statement: Node) -> tuple[Node, Node] | None:
        expression = statement.named_children[0] if statement.named_children else None
        if expression is None or expression.type != "assignment_expression":
            return None
        left = expression.child_by_field_name("left") or expression.named_children[0]
        right = expression.child_by_field_name("right") or expression.named_children[-1]
        return left, right

    def _import_with_names_info(
        self,
        node: Node,
        context: ScopeContext,
    ) -> tuple[str, int] | None:
        import_call = next(
            (
                invocation
                for invocation in self.document.descendants(node, "invocation_expression")
                if self.document.text(
                    invocation.child_by_field_name("function")
                    or invocation.named_children[0]
                ) == "PythonOps.ImportWithNames"
            ),
            None,
        )
        if import_call is None:
            return None
        import_args = self._argument_nodes(import_call)
        if len(import_args) < 2:
            return None
        try:
            module_name = decode_csharp_string(self.document.text(import_args[1]))
        except ValueError:
            module_name = self.expression(import_args[1], context).text
        level = -1
        level_match = re.search(r"-?\d+", self.document.text(import_args[-1]))
        if level_match:
            level = int(level_match.group(0))
        return module_name, level

    def _is_line_assignment(self, left: Node, right: Node, context: ScopeContext) -> int | None:
        name = self.document.text(left).strip()
        raw = self.document.text(right).strip()
        if name in context.line_identifiers and re.fullmatch(r"\d+", raw):
            return int(raw)
        return None

    def _lvalue(self, node: Node, context: ScopeContext, allocate: bool = True) -> str:
        raw = self.document.text(node)
        global_name = self._global_expression(raw)
        if global_name is not None:
            return global_name
        alias = context.lookup_alias(raw)
        if alias is not None:
            return alias
        if node.type == "identifier":
            identifier = raw
            return context.allocate_name(identifier) if allocate else context.identifier_aliases.get(identifier, decode_identifier(identifier))
        return self.expression(node, context).text

    def _emit_expression_statement(self, statement: Node, context: ScopeContext, writer: PythonWriter) -> None:
        assignment = self._assignment_nodes(statement)
        if assignment:
            left_node, right_node = assignment
            line = self._is_line_assignment(left_node, right_node, context)
            if line is not None:
                context.current_line = line
                return
            left_raw = self.document.text(left_node)
            right_raw = self.document.text(right_node)
            if (
                right_raw.endswith(".Target")
                and self._callsite_index(right_raw) is not None
            ):
                return
            if (
                any(right_raw.startswith(call) for call in SCAFFOLD_CALLS)
                and "PythonOps.Import" not in right_raw
            ):
                return
            if right_raw.strip() == "MissingParameter.Value":
                if left_node.type == "identifier":
                    context.identifier_aliases[self.document.text(left_node)] = ""
                return
            if "PythonOps.ImportWithNames" in right_raw:
                import_info = self._import_with_names_info(right_node, context)
                if import_info is not None and left_node.type == "identifier":
                    context.import_modules[self.document.text(left_node)] = import_info
                return
            left = self._lvalue(left_node, context)
            if left == "_":
                return
            if right_raw.strip() == "Uninitialized.Instance":
                writer.write("del %s" % left)
                context.semantic_statements += 1
                return
            if "PythonOps.ImportFrom" in right_raw:
                args = self._argument_nodes(right_node) if right_node.type == "invocation_expression" else []
                if len(args) >= 3:
                    module_var = self.document.text(args[1]).strip()
                    try:
                        imported = decode_csharp_string(self.document.text(args[2]))
                    except ValueError:
                        imported = self.expression(args[2], context).text
                    module_info = context.import_modules.get(module_var)
                    if module_info:
                        module_name, level = module_info
                        dots = "." * max(0, level)
                        alias = " as %s" % left if left != imported else ""
                        writer.write("from %s%s import %s%s" % (dots, module_name, imported, alias))
                        context.semantic_statements += 1
                        return
            if "PythonOps.ImportTop" in right_raw or "PythonOps.ImportBottom" in right_raw:
                match = re.search(r"Import(?:Top|Bottom)\([^,]+,\s*(\"(?:\\.|[^\"])*\")", right_raw)
                if match:
                    imported = decode_csharp_string(match.group(1))
                    bound = imported.split(".")[0] if "ImportTop" in right_raw else imported.split(".")[-1]
                    alias = " as %s" % left if left != bound else ""
                    writer.write("import %s%s" % (imported, alias))
                    context.semantic_statements += 1
                    return
            value = self.expression(right_node, context)
            # Function and class creation expressions intentionally have the
            # same text as their assignment target.  Emit the child scope
            # before applying the compiler-temporary self-assignment filter.
            if self._emit_child_expression(value, context, writer):
                return
            if left == value.text:
                self.stats["compiler_temporaries_elided"] += 1
                return
            if not self._is_python_assignment_target(left):
                if left_node.type == "identifier":
                    context.identifier_aliases[left_raw] = value.text
                self.stats["compiler_temporaries_elided"] += 1
                return
            if left in {"__name__", "__file__", "__package__", "__builtins__", "__path__"} and context.scope is None and context.current_line is None:
                return
            if context.scope is not None and context.scope.is_class and left in {"__doc__", "__module__"}:
                return
            if left == "__doc__" and context.scope is None and context.current_line is None:
                if value.text != "None":
                    writer.write(value.text)
                    context.semantic_statements += 1
                return
            if value.statement and value.statement.startswith(left + " "):
                writer.write(value.statement)
            else:
                writer.write("%s = %s" % (left, value.text))
            context.semantic_statements += 1
            return

        expression_node = statement.named_children[0] if statement.named_children else None
        raw = self.document.text(expression_node)
        if any(raw.startswith(call) for call in SCAFFOLD_CALLS):
            return
        if raw.startswith("PythonOps.ImportStar"):
            match = re.search(r"ImportStar\([^,]+,\s*(\"(?:\\.|[^\"])*\")", raw)
            if match:
                writer.write("from %s import *" % decode_csharp_string(match.group(1)))
                context.semantic_statements += 1
                return
        if raw.endswith(".RemoveAt(list.Count + -1)") or ".RemoveAt(" in raw and "Count + -1" in raw:
            return
        value = self.expression(expression_node, context)
        if value.statement:
            if not self._is_python_assignment_statement(value.statement):
                self.stats["invalid_statements_elided"] += 1
                return
            writer.write(value.statement)
        elif value.text not in {"None", ""}:
            writer.write(value.text)
        else:
            return
        context.semantic_statements += 1

    def _emit_return(self, statement: Node, context: ScopeContext, writer: PythonWriter) -> None:
        value_node = statement.child_by_field_name("value")
        if value_node is None and statement.named_children:
            value_node = statement.named_children[-1]
        if value_node is None:
            writer.write("return")
            context.semantic_statements += 1
            return
        if context.scope is not None and context.scope.is_class:
            return
        value = self.expression(value_node, context)
        if self._emit_child_expression(value, context, writer):
            writer.write("return %s" % value.text)
        else:
            writer.write("return %s" % value.text)
        context.semantic_statements += 1

    def _emit_throw(self, statement: Node, context: ScopeContext, writer: PythonWriter) -> None:
        value_node = statement.named_children[-1] if statement.named_children else None
        if value_node is None:
            writer.write("raise")
        else:
            value = self.expression(value_node, context)
            if value.statement == "raise":
                writer.write("raise")
            else:
                writer.write("raise %s" % value.text)
        context.semantic_statements += 1

    def _statement_body(self, statement: Node, field: str) -> Node | None:
        value = statement.child_by_field_name(field)
        if value is not None:
            return value
        return None

    def _emit_nested(self, node: Node | None, context: ScopeContext, writer: PythonWriter) -> None:
        if node is None:
            writer.write("pass")
        elif node.type == "block":
            before = len(writer.lines)
            self._emit_block(node, context, writer)
            if len(writer.lines) == before:
                writer.write("pass")
        else:
            self._emit_block(node.parent or node, context, writer, children=[node])

    def _emit_if(self, statement: Node, context: ScopeContext, writer: PythonWriter) -> None:
        condition_node = statement.child_by_field_name("condition")
        consequence = statement.child_by_field_name("consequence")
        alternative = statement.child_by_field_name("alternative")
        condition = self.expression(condition_node, context)
        with writer.block("if %s:" % condition.parenthesized(6)):
            self._emit_nested(consequence, context, writer)
        if alternative is not None:
            if alternative.type == "if_statement":
                # Emit an actual elif by rendering into a temporary writer and
                # replacing its first indentation-neutral token.
                temp = PythonWriter()
                self._emit_if(alternative, context, temp)
                lines = temp.lines
                if lines and lines[0].startswith("if "):
                    writer.write("el" + lines[0])
                    for line in lines[1:]:
                        writer.write(line)
            else:
                with writer.block("else:"):
                    before = len(writer.lines)
                    self._emit_nested(alternative, context, writer)
                    if len(writer.lines) == before:
                        writer.write("pass")
        context.semantic_statements += 1

    def _emit_while(self, statement: Node, context: ScopeContext, writer: PythonWriter) -> None:
        condition_node = statement.child_by_field_name("condition")
        body = statement.child_by_field_name("body")
        condition = self.expression(condition_node, context)
        body_children = list(body.named_children) if body and body.type == "block" else ([body] if body else [])

        guard_index = None
        guard_statement = None
        if condition.text == "True":
            for index, child in enumerate(body_children):
                if child.type == "if_statement":
                    consequence = child.child_by_field_name("consequence")
                    if consequence and any(item.type == "break_statement" for item in consequence.named_children):
                        guard_index, guard_statement = index, child
                        break
                if child.type not in {"local_declaration_statement"}:
                    break
        else_suite: list[Node] = []
        if guard_statement is not None:
            guard_condition = self.expression(guard_statement.child_by_field_name("condition"), context).text
            condition_text = guard_condition[4:] if guard_condition.startswith("not ") else "not (%s)" % guard_condition
            consequence = guard_statement.child_by_field_name("consequence")
            else_suite = [item for item in consequence.named_children if item.type != "break_statement"] if consequence else []
            body_children = body_children[guard_index + 1:]
        else:
            condition_text = condition.text
        if condition.precedence < 6 and guard_statement is None:
            condition_text = "(%s)" % condition_text
        with writer.block("while %s:" % condition_text):
            before = len(writer.lines)
            self._emit_block(body or statement, context, writer, children=body_children)
            if len(writer.lines) == before:
                writer.write("pass")
        if else_suite:
            with writer.block("else:"):
                self._emit_block(body or statement, context, writer, children=else_suite)
        context.semantic_statements += 1

    def _emit_csharp_for(
        self,
        statement: Node,
        context: ScopeContext,
        writer: PythonWriter,
    ) -> None:
        """Recover ILSpy ``for`` lowering as a Python ``while`` loop.

        IronPython emits this form when a source while-condition or update can
        return a light exception.  The generated initializer/update clauses
        are data-flow nodes; source-line markers distinguish their semantic
        assignments from exception transport.
        """
        initializer = statement.child_by_field_name("initializer")
        condition_node = statement.child_by_field_name("condition")
        update = statement.child_by_field_name("update")
        body = statement.child_by_field_name("body")

        if initializer is not None:
            if initializer.type == "assignment_expression":
                left = initializer.child_by_field_name("left") or initializer.named_children[0]
                right = initializer.child_by_field_name("right") or initializer.named_children[-1]
                line = self._is_line_assignment(left, right, context)
                if line is not None:
                    context.current_line = line

        condition = (
            self.expression(condition_node, context)
            if condition_node is not None else Expr("True")
        )
        with writer.block("while %s:" % condition.parenthesized(6)):
            before = len(writer.lines)
            body_nodes = (
                body.named_children
                if body is not None and body.type == "block"
                else ([body] if body is not None else [])
            )
            if "LightExceptions" in self.document.text(statement):
                self._emit_light_nodes(body_nodes, context, writer)
            elif body is not None:
                self._emit_block(body, context, writer, children=body_nodes)

            update_nodes = [
                child
                for child in statement.named_children
                if child is not initializer
                and child is not condition_node
                and child is not body
            ]
            if update is not None and update not in update_nodes:
                update_nodes.insert(0, update)
            if update_nodes:
                self._emit_light_nodes(update_nodes, context, writer)
            if len(writer.lines) == before:
                writer.write("pass")
        context.semantic_statements += 1

    def _loop_declaration(self, statement: Node, context: ScopeContext) -> tuple[str, Expr] | None:
        parts = self._variable_parts(statement)
        if len(parts) != 1 or parts[0][1] is None:
            return None
        identifier, initializer, _ = parts[0]
        binder = self._outer_callsite_binder(initializer)
        if binder is None or binder.kind != "operation" or binder.operation != "GetEnumeratorForIteration":
            return None
        iterator = self.expression(initializer, context)
        text = iterator.text
        if not (text.startswith("iter(") and text.endswith(")")):
            return None
        return identifier, Expr(text[5:-1])

    def _loop_assignment(self, statement: Node, context: ScopeContext) -> tuple[str, Expr] | None:
        assignment = self._assignment_nodes(statement)
        if assignment is None:
            return None
        left, right = assignment
        if left.type != "identifier":
            return None
        binder = self._outer_callsite_binder(right)
        if binder is None or binder.kind != "operation" or binder.operation != "GetEnumeratorForIteration":
            return None
        iterator = self.expression(right, context)
        if not (iterator.text.startswith("iter(") and iterator.text.endswith(")")):
            return None
        return self.document.text(left), Expr(iterator.text[5:-1])

    def _outer_callsite_binder(self, node: Node) -> Binder | None:
        current = node
        while current.type in {"parenthesized_expression", "cast_expression"} and current.named_children:
            current = current.named_children[-1]
        if current.type != "invocation_expression":
            return None
        function = current.child_by_field_name("function") or current.named_children[0]
        if not self.document.text(function).endswith(".Target"):
            return None
        receiver = function.child_by_field_name("expression")
        index = self._callsite_index(self.document.text(receiver))
        return self.binders.get(index) if index is not None else None

    def _source_loop_target(self, raw: str, context: ScopeContext) -> str:
        """Resolve a generated loop-current lvalue to its Python name."""
        global_name = self._global_expression(raw)
        if global_name is not None:
            return global_name
        alias = context.lookup_alias(raw)
        if alias is not None:
            return alias
        return context.allocate_name(raw)

    def _emit_for_try(
        self,
        statement: Node,
        enumerator: str,
        iterable: Expr,
        context: ScopeContext,
        writer: PythonWriter,
        light: bool = False,
        generator: bool = False,
    ) -> bool:
        canonical_enumerator = ScopeContext.canonical(enumerator)
        if (
            generator
            and canonical_enumerator in context.generator_consumed_enumerators
        ):
            return False
        raw = self.document.text(statement)
        if "PythonOps.ForLoopDispose" not in raw or enumerator not in raw:
            return False
        body = statement.child_by_field_name("body")
        if body is None:
            body = next((child for child in statement.named_children if child.type == "block"), None)
        if body is None:
            return False
        loop_node = next(
            (
                child
                for kind in ("while_statement", "for_statement")
                for child in self.document.descendants(body, kind)
                if enumerator + ".Key.MoveNext" in self.document.text(child)
            ),
            None,
        )
        if loop_node is None:
            return False
        loop_body = loop_node.child_by_field_name("body")
        if loop_body is None:
            return False
        children = list(loop_body.named_children)
        current_identifier: str | None = None
        current_index = -1
        unpack_array: str | None = None
        unpack_names: list[tuple[int, str]] = []
        setup_end = 0

        for index, child in enumerate(children):
            if child.type == "local_declaration_statement":
                for identifier, initializer, _ in self._variable_parts(child):
                    if initializer is None:
                        continue
                    init_raw = self.document.text(initializer)
                    if enumerator + ".Key.Current" in init_raw:
                        current_identifier = identifier
                        current_index = index
                        setup_end = index + 1
                    elif "GetEnumeratorValues" in init_raw:
                        unpack_array = identifier
                        setup_end = index + 1
                    elif unpack_array and re.search(r"\b" + re.escape(unpack_array) + r"\[(\d+)\]", init_raw):
                        match = re.search(r"\b" + re.escape(unpack_array) + r"\[(\d+)\]", init_raw)
                        unpack_names.append((int(match.group(1)), identifier))
                        setup_end = index + 1
            elif child.type == "expression_statement":
                assignment = self._assignment_nodes(child)
                if assignment and enumerator + ".Key.Current" in self.document.text(assignment[1]):
                    current_identifier = self.document.text(assignment[0])
                    current_index = index
                    setup_end = index + 1
                    continue
                if assignment and unpack_array:
                    left_node, right_node = assignment
                    match = re.search(
                        r"\b" + re.escape(unpack_array) + r"\[(\d+)\]",
                        self.document.text(right_node),
                    )
                    if match:
                        unpack_names.append((int(match.group(1)), self.document.text(left_node)))
                        setup_end = index + 1
                        continue
                # A source-line assignment marks the beginning of the loop body.
                if assignment and self._is_line_assignment(*assignment, context) is not None:
                    break
            if current_identifier is not None and index > current_index + 8:
                break

        if current_identifier is None:
            return False
        if generator:
            context.generator_consumed_enumerators.add(canonical_enumerator)
        if unpack_names:
            target_values = []
            for _, identifier in sorted(unpack_names):
                name = self._source_loop_target(identifier, context)
                name = self._valid_loop_target(name, identifier, context)
                context.add_alias(identifier, name)
                target_values.append(name)
            target = "(%s)" % ", ".join(target_values)
        else:
            if context.scope is not None and context.scope.is_generator:
                name = self._generator_loop_target(current_identifier, context)
            else:
                name = self._source_loop_target(current_identifier, context)
            name = self._valid_loop_target(name, current_identifier, context)
            context.add_alias(current_identifier, name)
            target = name

        semantic_children = children[setup_end:]
        with writer.block("for %s in %s:" % (target, iterable.text)):
            before = len(writer.lines)
            if generator:
                enumerators_before = set(context.loop_enumerators)
                context.generator_loop_depth += 1
                try:
                    self._emit_generator_nodes(semantic_children, context, writer)
                    for nested_enumerator in (
                        key for key in context.loop_enumerators
                        if key not in enumerators_before
                    ):
                        nested_iterable = context.loop_enumerators[nested_enumerator]
                        if self._emit_for_try(
                            statement,
                            nested_enumerator,
                            nested_iterable,
                            context,
                            writer,
                            generator=True,
                        ) or self._emit_generator_for_try(
                            statement,
                            context,
                            writer,
                            only_enumerator=nested_enumerator,
                        ):
                            break
                finally:
                    context.generator_loop_depth -= 1
            elif light:
                self._emit_light_nodes(semantic_children, context, writer)
            else:
                self._emit_block(loop_body, context, writer, children=semantic_children)
            if len(writer.lines) == before:
                writer.write("pass")

        body_children = list(body.named_children)
        if loop_node in body_children:
            position = body_children.index(loop_node)
            else_children = body_children[position + 1:]
        else:
            # A descendant loop is wrapped in ILSpy state labels/gotos.  Its
            # following siblings are continuation machinery, not Python's
            # optional ``for ... else`` suite.
            else_children = []
        exhaustion_returns = False
        if generator:
            move_guards = {
                ScopeContext.canonical(self.document.text(
                    assignment.child_by_field_name("left")
                    or assignment.named_children[0]
                ))
                for assignment in self.document.descendants(
                    loop_node, "assignment_expression"
                )
                if enumerator + ".Key.MoveNext" in ScopeContext.canonical(
                    self.document.text(
                        assignment.child_by_field_name("right")
                        or assignment.named_children[-1]
                    )
                )
            }
            for candidate in self.document.descendants(loop_node, "if_statement"):
                condition_raw = ScopeContext.canonical(
                    self.document.text(candidate.child_by_field_name("condition"))
                )
                if (
                    enumerator + ".Key.MoveNext" not in condition_raw
                    and not any(guard in condition_raw for guard in move_guards)
                ):
                    continue
                consequence = candidate.child_by_field_name("consequence")
                consequence_raw = self.document.text(consequence)
                if (
                    re.search(r"\.Item000\s*=\s*0\b", consequence_raw)
                    and re.search(r"\bgoto\s+end_IL_", consequence_raw)
                ):
                    exhaustion_returns = True
                    break
        if exhaustion_returns:
            with writer.block("else:"):
                writer.write("return")
                context.semantic_statements += 1
        elif else_children:
            # Dispose/reset statements are in the finally clause, not here; any
            # semantic statements following the loop are Python's ``for else``.
            with writer.block("else:"):
                before = len(writer.lines)
                if generator:
                    self._emit_generator_nodes(else_children, context, writer)
                elif light:
                    self._emit_light_nodes(else_children, context, writer)
                else:
                    self._emit_block(body, context, writer, children=else_children)
                if len(writer.lines) == before:
                    writer.write("pass")
        context.semantic_statements += 1
        return True

    def _python_user_try(self, node: Node) -> bool:
        catches = [child for child in node.named_children if child.type == "catch_clause"]
        return bool(catches) and any(
            "PythonOps.SetCurrentException" in self.document.text(catch)
            for catch in catches
        )

    def _find_python_user_try(self, node: Node) -> Node | None:
        candidates = [
            candidate
            for candidate in self.document.descendants(node, "try_statement")
            if candidate is not node and self._python_user_try(candidate)
        ]
        return min(candidates, key=lambda item: item.start_byte) if candidates else None

    def _line_value(self, statement: Node, context: ScopeContext) -> int | None:
        if statement.type != "expression_statement":
            return None
        assignment = self._assignment_nodes(statement)
        if assignment is None:
            return None
        return self._is_line_assignment(assignment[0], assignment[1], context)

    def _source_lines_in(self, node: Node, context: ScopeContext) -> set[int]:
        values = set()
        for statement in self.document.descendants(node, "expression_statement"):
            value = self._line_value(statement, context)
            if value is not None:
                values.add(value)
        return values

    @staticmethod
    def _looks_like_call(text: str) -> bool:
        return bool(re.match(r"(?:[A-Za-z_][A-Za-z0-9_\.]*|\(.+\))\(.*\)$", text, re.S))

    def _light_flush(
        self,
        state: LightState,
        context: ScopeContext,
        writer: PythonWriter,
    ) -> None:
        if state.pending is None or state.emitted_on_line:
            state.pending = None
            return
        value = state.pending
        if value.statement:
            if self._is_python_assignment_statement(value.statement):
                writer.write(value.statement)
            else:
                self.stats["invalid_statements_elided"] += 1
        elif self._looks_like_call(value.text):
            if context.pending_names:
                name = context.pending_names.pop(0)
                context.assigned_names.add(name)
                writer.write("%s = %s" % (name, value.text))
            else:
                writer.write(value.text)
        state.pending = None

    def _light_set_line(
        self,
        line: int,
        state: LightState,
        context: ScopeContext,
        writer: PythonWriter,
    ) -> None:
        if state.current_line is not None and state.current_line != line:
            self._light_flush(state, context, writer)
        state.current_line = line
        context.current_line = line
        state.emitted_on_line = False

    def _light_temp_assignment(
        self,
        identifier: str,
        value: Expr,
        context: ScopeContext,
        state: LightState,
    ) -> None:
        # A single IL temporary is often reused first for an imported module
        # and then for a member/call result.  Import provenance is valid only
        # until that next assignment; retaining it makes later temporaries
        # alias the obsolete module value.
        context.import_modules.pop(identifier, None)
        context.identifier_aliases[identifier] = value.text
        if value.statement or self._looks_like_call(value.text):
            state.pending = value

    def _is_source_lvalue(self, raw: str, context: ScopeContext) -> bool:
        alias = context.lookup_alias(raw)
        if alias is not None and context.scope is not None:
            return alias in context.scope.variable_names or alias in context.scope.cell_variables
        if raw in context.identifier_aliases and context.scope is not None:
            return context.identifier_aliases[raw] in context.scope.variable_names
        if any(marker in raw for marker in (
            "strongBox", "CallSite", ".Target", "mutableTuple",
        )):
            return False
        return self._global_expression(raw) is not None or any(
            token in raw for token in (".CurrentValue", ".Value", "[")
        )

    def _light_non_exception_branch(self, statement: Node) -> Node | None:
        condition = statement.child_by_field_name("condition")
        raw = self.document.text(condition)
        if "LightExceptions.IsLightException" not in raw:
            return None
        consequence = statement.child_by_field_name("consequence")
        alternative = statement.child_by_field_name("alternative")
        stripped = raw.strip()
        negative = stripped.startswith("!") or stripped.startswith("(!")
        return consequence if negative else alternative

    def _emit_light_nodes(
        self,
        nodes: Sequence[Node],
        context: ScopeContext,
        writer: PythonWriter,
        state: LightState | None = None,
    ) -> None:
        state = state or LightState()
        for statement in nodes:
            if statement.start_byte in context.skip_statement_bytes:
                continue
            line = self._line_value(statement, context)
            if line is not None:
                self._light_set_line(line, state, context, writer)
                continue
            if statement.type == "local_declaration_statement":
                for identifier, initializer, type_name in self._variable_parts(statement):
                    if initializer is None:
                        continue
                    raw = self.document.text(initializer)
                    if any(marker in raw for marker in (
                        "SetCurrentException", "GetGlobalContext", "GetGlobalArrayFromContext",
                        "GetParentContextFromFunction", "SaveCurrentException", "MakeClosureCell",
                    )):
                        continue
                    if type_name.startswith(("CallSite<", "Func<", "CodeContext", "List<FunctionStack>")):
                        continue
                    if type_name.startswith("Exception") and "PythonOps.MakeException" not in raw:
                        continue
                    if raw in context.import_modules:
                        context.import_modules[identifier] = context.import_modules[raw]
                        context.identifier_aliases[identifier] = (
                            context.identifier_at(raw, initializer.start_byte)
                            or decode_identifier(raw)
                        )
                        continue
                    value = self.expression(initializer, context)
                    if (
                        type_name.startswith("KeyValuePair<IEnumerator")
                        and value.text.startswith("iter(")
                        and value.text.endswith(")")
                    ):
                        context.loop_enumerators[identifier] = Expr(value.text[5:-1])
                        context.identifier_aliases[identifier] = identifier
                        state.pending = None
                        continue
                    if self._is_source_lvalue(identifier, context):
                        name = context.lookup_alias(identifier)
                        name = name or context.identifier_aliases.get(identifier)
                        if name and name in (context.scope.variable_names if context.scope else []):
                            writer.write("%s = %s" % (name, value.text))
                            state.emitted_on_line = True
                            state.pending = None
                        else:
                            self._light_temp_assignment(identifier, value, context, state)
                    else:
                        self._light_temp_assignment(identifier, value, context, state)
                continue
            if statement.type == "expression_statement":
                raw_statement = self.document.text(statement.named_children[0] if statement.named_children else statement)
                if any(raw_statement.startswith(call) for call in SCAFFOLD_CALLS) or raw_statement.startswith("PythonOps.ExceptionHandled"):
                    continue
                assignment = self._assignment_nodes(statement)
                if assignment is not None:
                    left_node, right_node = assignment
                    left_raw = self.document.text(left_node)
                    right_raw = self.document.text(right_node)
                    if "PythonOps.ImportWithNames" in right_raw:
                        import_info = self._import_with_names_info(
                            right_node, context
                        )
                        if import_info is not None and left_node.type == "identifier":
                            context.import_modules[left_raw] = import_info
                            context.identifier_aliases[left_raw] = import_info[0]
                        continue
                    if "PythonOps.ImportFrom" in right_raw:
                        invocation = next(
                            (
                                item for item in self.document.descendants(
                                    right_node, "invocation_expression"
                                )
                                if self.document.text(
                                    item.child_by_field_name("function")
                                    or item.named_children[0]
                                ) == "PythonOps.ImportFrom"
                            ),
                            None,
                        )
                        args = self._argument_nodes(invocation) if invocation else []
                        if len(args) >= 3:
                            module_var = self.document.text(args[1]).strip()
                            imported = decode_csharp_string(
                                self.document.text(args[2])
                            )
                            module_info = context.import_modules.get(module_var)
                            if module_info is not None:
                                module_name, level = module_info
                                left = self._lvalue(left_node, context)
                                alias = " as %s" % left if left != imported else ""
                                writer.write(
                                    "from %s%s import %s%s" % (
                                        "." * max(0, level), module_name,
                                        imported, alias,
                                    )
                                )
                                state.emitted_on_line = True
                                state.pending = None
                                continue
                    if "PythonOps.ImportTop" in right_raw or "PythonOps.ImportBottom" in right_raw:
                        match = re.search(
                            r"Import(?:Top|Bottom)\([^,]+,\s*(\"(?:\\.|[^\"])*\")",
                            right_raw,
                        )
                        if match:
                            imported = decode_csharp_string(match.group(1))
                            writer.write("import %s" % imported)
                            if left_node.type == "identifier":
                                bound = (
                                    imported.split(".")[0]
                                    if "ImportTop" in right_raw
                                    else imported.split(".")[-1]
                                )
                                context.import_modules.pop(left_raw, None)
                                context.identifier_aliases[left_raw] = bound
                            state.emitted_on_line = True
                            state.pending = None
                            continue
                    if (
                        right_raw.endswith(".Target")
                        and self._callsite_index(right_raw) is not None
                    ):
                        continue
                    if any(token in left_raw for token in ("flag", "lineUpdated")):
                        continue
                    if right_raw in {"null", "default(Exception)"} and not self._is_source_lvalue(left_raw, context):
                        continue
                    if right_raw.strip() == "Uninitialized.Instance":
                        if self._is_source_lvalue(left_raw, context):
                            left = self._lvalue(left_node, context)
                            writer.write("del %s" % left)
                            state.emitted_on_line = True
                            state.pending = None
                        continue
                    value = self.expression(right_node, context)
                    if self._is_source_lvalue(left_raw, context):
                        left = self._lvalue(left_node, context)
                        if self._emit_child_expression(value, context, writer):
                            state.emitted_on_line = True
                            state.pending = None
                            continue
                        if not self._is_python_assignment_target(left):
                            if left_node.type == "identifier":
                                self._light_temp_assignment(left_raw, value, context, state)
                            self.stats["compiler_temporaries_elided"] += 1
                            continue
                        if left == value.text:
                            self.stats["compiler_temporaries_elided"] += 1
                            continue
                        if value.statement and value.statement.startswith(left + " "):
                            writer.write(value.statement)
                        else:
                            writer.write("%s = %s" % (left, value.text))
                        state.emitted_on_line = True
                        state.pending = None
                    elif (
                        context.scope is not None
                        and context.scope.is_generator
                        and self._generator_tuple_slot(left_raw) is not None
                    ):
                        slot = self._generator_tuple_slot(left_raw)
                        context.generator_temp_slots[slot] = value.text
                        if value.statement or self._looks_like_call(value.text):
                            state.pending = value
                    elif left_node.type == "identifier":
                        self._light_temp_assignment(left_raw, value, context, state)
                    continue
                value = self.expression(statement.named_children[0], context)
                if value.statement:
                    if self._is_python_assignment_statement(value.statement):
                        writer.write(value.statement)
                        state.emitted_on_line = True
                    else:
                        self.stats["invalid_statements_elided"] += 1
                    state.pending = None
                elif self._looks_like_call(value.text):
                    state.pending = value
                continue
            if statement.type == "if_statement":
                non_exception = self._light_non_exception_branch(statement)
                if "LightExceptions.IsLightException" in self.document.text(statement.child_by_field_name("condition")):
                    if non_exception is not None:
                        nested = non_exception.named_children if non_exception.type == "block" else [non_exception]
                        self._emit_light_nodes(nested, context, writer, state)
                    continue
                raw = self.document.text(statement)
                if "UpdateStackTrace" in raw and not self._source_lines_in(statement, context):
                    continue
                if not self._source_lines_in(statement, context) and "flag" in raw and "PythonOps." not in raw:
                    continue
                condition = self.expression(statement.child_by_field_name("condition"), context)
                self._light_flush(state, context, writer)
                with writer.block("if %s:" % condition.parenthesized(6)):
                    consequence = statement.child_by_field_name("consequence")
                    before = len(writer.lines)
                    nested = consequence.named_children if consequence and consequence.type == "block" else ([consequence] if consequence else [])
                    self._emit_light_nodes(nested, context, writer, LightState(state.current_line))
                    if len(writer.lines) == before:
                        writer.write("pass")
                alternative = statement.child_by_field_name("alternative")
                if alternative is not None:
                    with writer.block("else:"):
                        before = len(writer.lines)
                        nested = alternative.named_children if alternative.type == "block" else [alternative]
                        self._emit_light_nodes(nested, context, writer, LightState(state.current_line))
                        if len(writer.lines) == before:
                            writer.write("pass")
                state.emitted_on_line = True
                continue
            if statement.type == "return_statement":
                value_node = statement.child_by_field_name("value")
                if value_node is None and statement.named_children:
                    value_node = statement.named_children[-1]
                value = self.expression(value_node, context) if value_node else Expr("None")
                writer.write("return %s" % value.text)
                state.emitted_on_line = True
                state.pending = None
                continue
            if statement.type == "throw_statement":
                self._emit_throw(statement, context, writer)
                state.emitted_on_line = True
                state.pending = None
                continue
            if statement.type == "try_statement":
                emitted = False
                for enumerator, iterable in list(context.loop_enumerators.items()):
                    if self._emit_for_try(
                        statement, enumerator, iterable, context, writer, light=True
                    ):
                        emitted = True
                        break
                if not emitted:
                    emitted = self._emit_try(statement, context, writer)
                if emitted:
                    state.emitted_on_line = True
                continue
            if statement.type == "break_statement":
                writer.write("break")
                state.emitted_on_line = True
                state.pending = None
                continue
            if statement.type == "continue_statement":
                writer.write("continue")
                state.emitted_on_line = True
                state.pending = None
                continue
            if statement.type in {"goto_statement", "labeled_statement"}:
                continue
            if statement.type == "while_statement":
                self._light_flush(state, context, writer)
                if "LightExceptions" in self.document.text(statement):
                    body = statement.child_by_field_name("body")
                    with writer.block("while True:"):
                        before = len(writer.lines)
                        nested = (
                            body.named_children
                            if body is not None and body.type == "block"
                            else ([body] if body is not None else [])
                        )
                        self._emit_light_nodes(
                            nested, context, writer, LightState(state.current_line)
                        )
                        if len(writer.lines) == before:
                            writer.write("pass")
                else:
                    self._emit_while(statement, context, writer)
                state.emitted_on_line = True
                continue
            if statement.type == "for_statement":
                self._light_flush(state, context, writer)
                self._emit_csharp_for(statement, context, writer)
                state.emitted_on_line = True
                continue
        self._light_flush(state, context, writer)

    def _prepare_temp_aliases_before(
        self,
        root: Node,
        stop_byte: int,
        context: ScopeContext,
    ) -> None:
        statements: list[Node] = []
        statements.extend(self.document.descendants(root, "local_declaration_statement"))
        statements.extend(self.document.descendants(root, "expression_statement"))
        for statement in sorted(statements, key=lambda item: item.start_byte):
            if statement.start_byte >= stop_byte:
                break
            if statement.type == "local_declaration_statement":
                for identifier, initializer, type_name in self._variable_parts(statement):
                    if initializer is None or type_name.startswith(("CallSite<", "Func<", "CodeContext", "Exception")):
                        continue
                    raw = self.document.text(initializer)
                    if "CheckException" in raw or "SetCurrentException" in raw:
                        continue
                    value = self.expression(initializer, context)
                    context.identifier_aliases[identifier] = value.text
            else:
                assignment = self._assignment_nodes(statement)
                if assignment is None or assignment[0].type != "identifier":
                    continue
                raw = self.document.text(assignment[1])
                if "CheckException" in raw or "SetCurrentException" in raw:
                    continue
                value = self.expression(assignment[1], context)
                context.identifier_aliases[self.document.text(assignment[0])] = value.text

    def _handler_records(
        self,
        catch_body: Node,
        context: ScopeContext,
    ) -> list[tuple[str, str | None, list[Node]]]:
        records: list[tuple[str, str | None, list[Node]]] = []
        for invocation in self.document.descendants(catch_body, "invocation_expression"):
            function = invocation.child_by_field_name("function") or invocation.named_children[0]
            if self.document.text(function) != "PythonOps.CheckException":
                continue
            self._prepare_temp_aliases_before(catch_body, invocation.start_byte, context)
            args = self._argument_nodes(invocation)
            if len(args) < 3:
                continue
            exception_type = self.expression(args[2], context).text
            statement = invocation
            while statement.parent is not None and statement.type not in {
                "local_declaration_statement", "expression_statement"
            }:
                statement = statement.parent
            if statement.type not in {"local_declaration_statement", "expression_statement"} or statement.parent is None:
                continue
            assignment_names = []
            ancestor = invocation.parent
            while ancestor is not None and ancestor.start_byte >= statement.start_byte:
                if ancestor.type == "assignment_expression":
                    left = ancestor.child_by_field_name("left") or ancestor.named_children[0]
                    if left.type == "identifier":
                        assignment_names.append(self.document.text(left))
                ancestor = ancestor.parent
            if statement.type == "local_declaration_statement":
                assignment_names.extend(
                    identifier for identifier, initializer, _ in self._variable_parts(statement)
                    if initializer is not None
                )
            block = statement.parent
            siblings = list(block.named_children)
            try:
                position = siblings.index(statement)
            except ValueError:
                continue
            condition_node = next(
                (
                    item for item in siblings[position + 1:]
                    if item.type == "if_statement"
                    and any(name in self.document.text(item.child_by_field_name("condition")) for name in assignment_names)
                ),
                None,
            )
            if condition_node is None:
                continue
            condition_raw = self.document.text(condition_node.child_by_field_name("condition"))
            intervening = siblings[position + 1:siblings.index(condition_node)]
            null_names = set()
            for item in intervening:
                if item.type == "local_declaration_statement":
                    for identifier, initializer, _ in self._variable_parts(item):
                        if initializer is not None and self.document.text(initializer).strip() in {
                            "null", "default(object)",
                        }:
                            null_names.add(identifier)
                elif item.type == "expression_statement":
                    assignment = self._assignment_nodes(item)
                    if (
                        assignment is not None
                        and assignment[0].type == "identifier"
                        and self.document.text(assignment[1]).strip() in {
                            "null", "default(object)",
                        }
                    ):
                        null_names.add(self.document.text(assignment[0]))
            compares_nonnull = "!= null" in condition_raw or any(
                re.search(
                    r"\b(?:%s)\b\s*!=\s*\b%s\b|\b%s\b\s*!=\s*\b(?:%s)\b" % (
                        "|".join(map(re.escape, assignment_names)),
                        re.escape(null_name),
                        re.escape(null_name),
                        "|".join(map(re.escape, assignment_names)),
                    ),
                    condition_raw,
                )
                for null_name in null_names
            )
            compares_null = "== null" in condition_raw or any(
                re.search(
                    r"\b(?:%s)\b\s*==\s*\b%s\b|\b%s\b\s*==\s*\b(?:%s)\b" % (
                        "|".join(map(re.escape, assignment_names)),
                        re.escape(null_name),
                        re.escape(null_name),
                        "|".join(map(re.escape, assignment_names)),
                    ),
                    condition_raw,
                )
                for null_name in null_names
            )
            if compares_nonnull:
                body = condition_node.child_by_field_name("consequence")
                body_nodes = list(body.named_children) if body and body.type == "block" else ([body] if body else [])
            elif compares_null:
                body_nodes = siblings[siblings.index(condition_node) + 1:]
            else:
                continue
            body_raw = "\n".join(self.document.text(item) for item in body_nodes)
            target = None
            if any(re.search(r"\b" + re.escape(name) + r"\b", body_raw) for name in assignment_names):
                target = context.pending_names.pop(0) if context.pending_names else "_error"
                context.assigned_names.add(target)
                for name in assignment_names:
                    context.identifier_aliases[name] = target
                for item in body_nodes:
                    if item.type == "expression_statement" and self.document.text(item).startswith("PythonOps.BuildExceptionInfo"):
                        break
                    if item.type != "local_declaration_statement":
                        continue
                    for identifier, initializer, type_name in self._variable_parts(item):
                        if initializer is None or type_name.startswith(("CallSite<", "Func<", "CodeContext", "Exception")):
                            continue
                        value = self.expression(initializer, context)
                        context.identifier_aliases[identifier] = value.text
            records.append((exception_type, target, body_nodes))

        unique: list[tuple[str, str | None, list[Node]]] = []
        seen: set[tuple[str, int]] = set()
        for record in records:
            key = (record[0], record[2][0].start_byte if record[2] else -1)
            if key not in seen:
                seen.add(key)
                unique.append(record)
        return unique

    def _handler_semantic_nodes(self, nodes: Sequence[Node], context: ScopeContext) -> list[Node]:
        start = 0
        for index, node in enumerate(nodes):
            if node.type == "expression_statement" and self.document.text(node).startswith("PythonOps.BuildExceptionInfo"):
                start = index + 1
                break
        # Retain the line marker following BuildExceptionInfo; light emission
        # uses it to flush the correct source expression.
        return list(nodes[start:])

    def _recover_python_try(
        self,
        user_try: Node,
        context: ScopeContext,
        writer: PythonWriter,
        finally_clause: Node | None = None,
    ) -> bool:
        catches = [child for child in user_try.named_children if child.type == "catch_clause"]
        if not catches:
            return False
        catch_body = catches[0].child_by_field_name("body")
        if catch_body is None:
            catch_body = next((child for child in catches[0].named_children if child.type == "block"), None)
        body = user_try.child_by_field_name("body")
        if body is None or catch_body is None:
            return False

        region_lines = self._source_lines_in(user_try, context)
        with writer.block("try:"):
            before = len(writer.lines)
            self._emit_light_nodes(body.named_children, context, writer)
            if len(writer.lines) == before:
                writer.write("pass")

        handlers = self._handler_records(catch_body, context)
        if handlers:
            for exception_type, target, handler_nodes in handlers:
                suffix = " as %s" % target if target else ""
                with writer.block("except %s%s:" % (exception_type, suffix)):
                    before = len(writer.lines)
                    semantic = self._handler_semantic_nodes(handler_nodes, context)
                    self._emit_light_nodes(semantic, context, writer)
                    if len(writer.lines) == before:
                        if (
                            context.scope is not None
                            and context.scope.is_generator
                            and re.search(
                                r"\.Item000\s*=\s*0\b",
                                "\n".join(self.document.text(node) for node in handler_nodes),
                            )
                        ):
                            writer.write("return")
                        else:
                            writer.write("raise")
        else:
            with writer.block("except:"):
                before = len(writer.lines)
                semantic = self._handler_semantic_nodes(catch_body.named_children, context)
                self._emit_light_nodes(semantic, context, writer)
                if len(writer.lines) == before:
                    if (
                        context.scope is not None
                        and context.scope.is_generator
                        and re.search(
                            r"\.Item000\s*=\s*0\b",
                            self.document.text(catch_body),
                        )
                    ):
                        writer.write("return")
                    else:
                        writer.write("raise")

        # The light-exception duplicate follows the direct CLR catch path in
        # the same generated block.  Mark repeated-region siblings as consumed,
        # while preserving the first source line outside this try statement.
        parent = user_try.parent
        if parent is not None and parent.type == "block":
            siblings = list(parent.named_children)
            position = siblings.index(user_try)
            for sibling in siblings[position + 1:]:
                lines = self._source_lines_in(sibling, context)
                if lines and not lines.issubset(region_lines):
                    break
                context.skip_statement_bytes.add(sibling.start_byte)

            # A guarded block after the merge is Python's try/else suite.
            for sibling in siblings[position + 1:]:
                if sibling.start_byte in context.skip_statement_bytes:
                    continue
                if sibling.type != "if_statement":
                    break
                condition_raw = self.document.text(sibling.child_by_field_name("condition"))
                if re.fullmatch(r"\(?[A-Za-z_][A-Za-z0-9_]*\)?", condition_raw.strip()):
                    consequence = sibling.child_by_field_name("consequence")
                    with writer.block("else:"):
                        nested = consequence.named_children if consequence and consequence.type == "block" else ([consequence] if consequence else [])
                        self._emit_light_nodes(nested, context, writer)
                    context.skip_statement_bytes.add(sibling.start_byte)
                break

        if finally_clause is not None:
            finally_body = next(
                (child for child in finally_clause.named_children if child.type == "block"),
                None,
            )
            if finally_body is not None:
                with writer.block("finally:"):
                    before = len(writer.lines)
                    self._emit_light_nodes(finally_body.named_children, context, writer)
                    if len(writer.lines) == before:
                        writer.write("pass")
        context.semantic_statements += 1
        return True

    def _recover_returning_finally(
        self,
        statement: Node,
        context: ScopeContext,
        writer: PythonWriter,
    ) -> bool:
        """Recover a source ``finally: return`` traceback wrapper.

        IronPython tracks an active exception in a CLR local so a return from
        the source finally suite suppresses it with Python semantics.  ILSpy
        renders the resulting nested catch/rethrow/empty-catch structure even
        though only the innermost try body and final result assignment are
        source operations.
        """
        finally_clause = next(
            (
                child for child in statement.named_children
                if child.type == "finally_clause"
            ),
            None,
        )
        if finally_clause is None:
            return False
        finally_raw = self.document.text(finally_clause)
        if not (
            "PythonOps.UpdateStackTrace" in finally_raw
            and re.search(r"\bresult\s*=", finally_raw)
            and re.search(r"\bnum\s*=\s*1\b", finally_raw)
        ):
            return False

        nested_tries = [
            item
            for item in self.document.descendants(statement, "try_statement")
            if item is not statement
        ]
        if not nested_tries:
            return False
        semantic_try = max(
            nested_tries,
            key=lambda item: (
                len(self._source_lines_in(item, context)),
                -(item.end_byte - item.start_byte),
            ),
        )
        semantic_body = semantic_try.child_by_field_name("body")
        if semantic_body is None:
            return False

        result_assignment = next(
            (
                assignment
                for assignment in self.document.descendants(
                    finally_clause, "assignment_expression"
                )
                if self.document.text(
                    assignment.child_by_field_name("left")
                    or assignment.named_children[0]
                ).strip() == "result"
            ),
            None,
        )
        if result_assignment is None:
            return False

        with writer.block("try:"):
            before = len(writer.lines)
            self._emit_block(semantic_body, context, writer)
            if len(writer.lines) == before:
                writer.write("pass")
        result_node = (
            result_assignment.child_by_field_name("right")
            or result_assignment.named_children[-1]
        )
        with writer.block("finally:"):
            writer.write("return %s" % self.expression(result_node, context).text)

        if statement.parent is not None and statement.parent.type == "block":
            siblings = list(statement.parent.named_children)
            position = siblings.index(statement)
            for sibling in siblings[position + 1:]:
                if "return result" in self.document.text(sibling):
                    context.skip_statement_bytes.add(sibling.start_byte)
                elif not self._source_lines_in(sibling, context):
                    context.skip_statement_bytes.add(sibling.start_byte)
                else:
                    break
        context.semantic_statements += 1
        return True

    def _emit_try(self, statement: Node, context: ScopeContext, writer: PythonWriter) -> bool:
        raw = self.document.text(statement)
        if self._recover_returning_finally(statement, context, writer):
            return True
        if self._python_user_try(statement):
            return self._recover_python_try(statement, context, writer)
        nested_user_try = self._find_python_user_try(statement)
        structural_finally = next(
            (child for child in statement.named_children if child.type == "finally_clause"),
            None,
        )
        if nested_user_try is not None and structural_finally is not None:
            finally_lines = self._source_lines_in(structural_finally, context)
            if finally_lines and "RestoreCurrentException" not in self.document.text(structural_finally):
                return self._recover_python_try(
                    nested_user_try,
                    context,
                    writer,
                    finally_clause=structural_finally,
                )
        for enumerator, iterable in list(context.loop_enumerators.items()):
            if self._emit_for_try(statement, enumerator, iterable, context, writer):
                return True
        if "PythonOps.UpdateStackTrace" in raw and "PythonOps.CheckException" not in raw:
            # Compiler-injected traceback wrapper.  Its body has already been
            # selected as the semantic block when outermost; unwrap nested forms.
            body = statement.child_by_field_name("body")
            catches = [child for child in statement.named_children if child.type == "catch_clause"]
            if catches and all("PythonOps.UpdateStackTrace" in self.document.text(item) for item in catches):
                if body is not None:
                    self._emit_block(body, context, writer)
                return True
        finally_clause = next(
            (child for child in statement.named_children if child.type == "finally_clause"),
            None,
        )
        catches = [child for child in statement.named_children if child.type == "catch_clause"]
        if finally_clause and any(marker in self.document.text(finally_clause) for marker in (
            "RemoveAt", "ForLoopDispose", "RestoreCurrentException"
        )) and not catches:
            body = statement.child_by_field_name("body")
            if body is not None:
                self._emit_block(body, context, writer)
            return True

        # Straight C# try/catch is uncommon in serialized Python because
        # LightExceptions expands most handlers.  Preserve simple forms exactly.
        if catches and "PythonOps.CheckException" not in raw and "LightExceptions" not in raw:
            body = statement.child_by_field_name("body")
            with writer.block("try:"):
                self._emit_nested(body, context, writer)
            for catch in catches:
                declaration = next(
                    (child for child in catch.named_children if child.type == "catch_declaration"),
                    None,
                )
                name = ""
                if declaration is not None:
                    name_node = declaration.child_by_field_name("name")
                    if name_node is not None:
                        name = " as " + decode_identifier(self.document.text(name_node))
                catch_body = catch.child_by_field_name("body")
                with writer.block("except Exception%s:" % name):
                    self._emit_nested(catch_body, context, writer)
            if finally_clause is not None:
                finally_body = next(
                    (child for child in finally_clause.named_children if child.type == "block"),
                    None,
                )
                with writer.block("finally:"):
                    self._emit_nested(finally_body, context, writer)
            context.semantic_statements += 1
            return True
        return False

    def decompile(self) -> tuple[str, dict[str, Any]]:
        nodes = self.document.methods.get(self.module_method)
        if not nodes:
            nodes = next(
                (values for name, values in self.document.methods.items() if name.startswith(self.module_method)),
                [],
            )
        if not nodes:
            raise ValueError("module body method unavailable")
        writer = PythonWriter()
        writer.write("# -*- coding: utf-8 -*-")
        writer.write("# Reconstructed from IronPython 2.7.12 cached code.")
        writer.write("# Original comments, whitespace, and equivalent syntax were not serialized.")
        context = ScopeContext(self, None)
        self._prepare_context(nodes[0], context)
        body = self._semantic_block(nodes[0], module=True)
        self._emit_block(body, context, writer, skip_scaffold_prefix=True)

        # Ensure every root scope remains navigable even if ILSpy lowered its
        # creation through an unresolved temporary sequence.
        missing = [
            scope for scope in self.scopes
            if scope.parent is None and id(scope) not in context.emitted_children
            and not scope.is_lambda and not scope.is_comprehension
        ]
        for scope in sorted(missing, key=lambda item: item.source_start_index):
            if writer.lines and writer.lines[-1]:
                writer.write()
            context.emitted_children.add(id(scope))
            self._emit_scope(scope, writer)

        source = writer.render()
        report = {
            "module": self.module_name,
            "binders_declared": len(self.binders),
            "binders_inverted": sum(value for key, value in self.stats.items() if key.startswith("binder_")),
            "scope_count": len(self.scopes),
            "root_scopes": len([scope for scope in self.scopes if scope.parent is None]),
            "diagnostic_count": len(self.diagnostics),
            "diagnostics": [diagnostic.__dict__ for diagnostic in self.diagnostics],
            "operation_counts": dict(sorted(self.stats.items())),
        }
        return source, report


def load_decompiler(
    module_name: str,
    source_path: Path,
    metadata_path: Path,
    functions_path: Path,
) -> IronPythonDecompiler:
    return IronPythonDecompiler(
        module_name,
        CSharpDocument(source_path),
        json.loads(metadata_path.read_text(encoding="utf-8")),
        json.loads(functions_path.read_text(encoding="utf-8")),
    )


def decompile_corpus(source_root: Path, recovery_root: Path, output_root: Path) -> dict[str, Any]:
    output_root.mkdir(parents=True, exist_ok=True)
    reports: list[dict[str, Any]] = []
    failures: list[dict[str, str]] = []
    metadata_paths = sorted((recovery_root / "python-metadata").glob("*.json"))
    for metadata_path in metadata_paths:
        module_name = metadata_path.stem
        source_path = source_root / module_name / "DLRCachedCode.cs"
        functions_path = recovery_root / "python-functions" / metadata_path.name
        try:
            decompiler = load_decompiler(module_name, source_path, metadata_path, functions_path)
            source, report = decompiler.decompile()
            destination = output_root / (module_name + ".py")
            destination.write_text(source, encoding="utf-8")
            report["source"] = str(destination)
            report["source_line_count"] = len(source.splitlines())
            report["compiler_scaffold_counts"] = {
                marker: source.count(marker)
                for marker in (
                    "strongBox", "mutableTuple", "CallSite", "__ipy_",
                    "LightExceptions", "globalArrayFromContext",
                    "globalContext", "PythonOps", "ScriptingRuntimeHelpers",
                    "DLRCachedCode",
                )
                if marker in source
            }
            reports.append(report)
        except Exception as error:
            failures.append({
                "module": module_name,
                "error": "%s: %s" % (type(error).__name__, error),
            })
    diagnostic_kinds = Counter(
        diagnostic["kind"]
        for report in reports
        for diagnostic in report["diagnostics"]
    )
    scaffold_counts = Counter(
        {
            marker: sum(
                report["compiler_scaffold_counts"].get(marker, 0)
                for report in reports
            )
            for marker in {
                marker
                for report in reports
                for marker in report["compiler_scaffold_counts"]
            }
        }
    )
    summary = {
        "schema_version": 2,
        "modules_requested": len(metadata_paths),
        "modules_emitted": len(reports),
        "module_failures": failures,
        "diagnostic_count": sum(item["diagnostic_count"] for item in reports),
        "diagnostic_kind_counts": dict(sorted(diagnostic_kinds.items())),
        "scopes": sum(item["scope_count"] for item in reports),
        "source_lines": sum(item["source_line_count"] for item in reports),
        "compiler_scaffold_counts": dict(sorted(scaffold_counts.items())),
        "modules_with_compiler_scaffolding": [
            report["module"]
            for report in reports
            if report["compiler_scaffold_counts"]
        ],
        "reports": reports,
    }
    (output_root / "decompilation-report.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("recovery_root", type=Path)
    parser.add_argument("output_root", type=Path)
    parser.add_argument(
        "--source-root",
        type=Path,
        help="reference-aware ILSpy project root (defaults to recovery_root/source)",
    )
    parser.add_argument("--module", help="decompile only one assembly/module name")
    args = parser.parse_args()
    recovery_root = args.recovery_root.resolve()
    source_root = (args.source_root or recovery_root / "source").resolve()
    output_root = args.output_root.resolve()
    if args.module:
        metadata_path = recovery_root / "python-metadata" / (args.module + ".json")
        functions_path = recovery_root / "python-functions" / (args.module + ".json")
        source_path = source_root / args.module / "DLRCachedCode.cs"
        output_root.mkdir(parents=True, exist_ok=True)
        decompiler = load_decompiler(args.module, source_path, metadata_path, functions_path)
        source, report = decompiler.decompile()
        destination = output_root / (args.module + ".py")
        destination.write_text(source, encoding="utf-8")
        (output_root / (args.module + ".report.json")).write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        print(json.dumps(report, sort_keys=True))
        return 0
    summary = decompile_corpus(source_root, recovery_root, output_root)
    print(json.dumps({key: value for key, value in summary.items() if key != "reports"}, sort_keys=True))
    return 0 if not (
        summary["module_failures"]
        or summary["modules_with_compiler_scaffolding"]
    ) else 2


if __name__ == "__main__":
    raise SystemExit(main())
