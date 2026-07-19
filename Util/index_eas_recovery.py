#!/usr/bin/env python3
"""Index Python scope metadata and assembly dependencies after EAS recovery.

This is a static post-processor for output from ``reconstruct_eas.py``.  It
never loads or executes a recovered assembly.
"""

from __future__ import annotations

import argparse
import ast
import csv
import json
from pathlib import Path
import re
import subprocess
from typing import Any, Iterator


CALL = "PythonOps.MakeFunctionCode("
FLAG_VALUES = {
    "ArgumentList": 0x04,
    "KeywordDictionary": 0x08,
    "Generator": 0x20,
    "FutureDivision": 0x2000,
    "CanSetSysExcInfo": 0x4000,
    "ContainsTryFinally": 0x8000,
}


def scan_balanced(text: str, start: int, opening: str, closing: str) -> int:
    if text[start] != opening:
        raise ValueError("balanced scan does not start at %r" % opening)
    depth = 1
    index = start + 1
    quote: str | None = None
    verbatim = False
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
        if char == "/" and nxt == "/":
            newline = text.find("\n", index + 2)
            index = len(text) if newline < 0 else newline + 1
            continue
        if char == "/" and nxt == "*":
            end = text.find("*/", index + 2)
            if end < 0:
                raise ValueError("unterminated block comment")
            index = end + 2
            continue
        if char in ('"', "'"):
            quote = char
            verbatim = char == '"' and index > 0 and text[index - 1] == "@"
            index += 1
            continue
        if char == opening:
            depth += 1
        elif char == closing:
            depth -= 1
            if depth == 0:
                return index
        index += 1
    raise ValueError("unterminated %s...%s expression" % (opening, closing))


def iter_call_arguments(text: str) -> Iterator[list[str]]:
    offset = 0
    while True:
        found = text.find(CALL, offset)
        if found < 0:
            return
        opening = found + len(CALL) - 1
        closing = scan_balanced(text, opening, "(", ")")
        yield split_arguments(text[opening + 1:closing])
        offset = closing + 1


def split_arguments(text: str) -> list[str]:
    arguments: list[str] = []
    start = 0
    parens = brackets = braces = angles = 0
    quote: str | None = None
    verbatim = False
    index = 0
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
        if char == "/" and nxt == "/":
            newline = text.find("\n", index + 2)
            index = len(text) if newline < 0 else newline + 1
            continue
        if char == "/" and nxt == "*":
            end = text.find("*/", index + 2)
            if end < 0:
                raise ValueError("unterminated block comment")
            index = end + 2
            continue
        if char in ('"', "'"):
            quote = char
            verbatim = char == '"' and index > 0 and text[index - 1] == "@"
        elif char == "(":
            parens += 1
        elif char == ")":
            parens -= 1
        elif char == "[":
            brackets += 1
        elif char == "]":
            brackets -= 1
        elif char == "{":
            braces += 1
        elif char == "}":
            braces -= 1
        elif char == "<":
            angles += 1
        elif char == ">" and angles:
            angles -= 1
        elif char == "," and not (parens or brackets or braces or angles):
            arguments.append(text[start:index].strip())
            start = index + 1
        index += 1
    arguments.append(text[start:].strip())
    return arguments


def decode_csharp_string(value: str) -> str | None:
    value = value.strip()
    if value == "null":
        return None
    if value.startswith('@"') and value.endswith('"'):
        return value[2:-1].replace('""', '"')
    if value.startswith('"') and value.endswith('"'):
        return ast.literal_eval(value)
    raise ValueError("not a C# string literal: %s" % value[:80])


def string_array(value: str) -> list[str] | None:
    value = value.strip()
    if value == "null":
        return None
    if re.fullmatch(r"new string\[0\](?:\s*\{\s*\})?", value):
        return []
    strings = []
    index = 0
    while index < len(value):
        if value[index] == '"' or value.startswith('@"', index):
            start = index - 1 if value.startswith('@"', index) else index
            if value[start] == "@":
                index += 2
                while index < len(value):
                    if value[index:index + 2] == '""':
                        index += 2
                    elif value[index] == '"':
                        index += 1
                        break
                    else:
                        index += 1
            else:
                index += 1
                while index < len(value):
                    if value[index] == "\\":
                        index += 2
                    elif value[index] == '"':
                        index += 1
                        break
                    else:
                        index += 1
            strings.append(decode_csharp_string(value[start:index]))
        else:
            index += 1
    return strings


def flags(value: str) -> tuple[int | None, list[str]]:
    value = value.strip()
    numeric = re.fullmatch(r"\(FunctionAttributes\)(0x[0-9a-fA-F]+|\d+)", value)
    if numeric:
        bits = int(numeric.group(1), 0)
    else:
        names = re.findall(r"FunctionAttributes\.([A-Za-z0-9_]+)", value)
        if not names:
            return None, [value]
        bits = sum(FLAG_VALUES.get(name, 0) for name in names if name != "None")
    labels = [name for name, bit in FLAG_VALUES.items() if bits & bit]
    unknown = bits & ~sum(FLAG_VALUES.values())
    if unknown:
        labels.append("unknown:0x%x" % unknown)
    return bits, labels


def target_method(delegate_expression: str) -> str | None:
    matches = re.findall(r"&([A-Za-z0-9_]+)", delegate_expression)
    return matches[-1] if matches else None


def method_source_lines(text: str, method: str | None) -> list[int]:
    if not method:
        return []
    declaration = re.search(
        r"(?:public|private|internal|protected)\s+static\s+[^\n{;]+\b" +
        re.escape(method) + r"\s*\(", text,
    )
    if not declaration:
        return []
    opening = text.find("{", declaration.end())
    if opening < 0:
        return []
    try:
        closing = scan_balanced(text, opening, "{", "}")
    except ValueError:
        return []
    return sorted({int(value) for value in re.findall(r"\bline\s*=\s*(\d+)\s*;", text[opening:closing + 1])})


def function_records(text: str) -> list[dict[str, Any]]:
    recovered: dict[tuple[Any, ...], dict[str, Any]] = {}
    for arguments in iter_call_arguments(text):
        if len(arguments) != 14:
            raise ValueError("MakeFunctionCode has %d arguments, expected 14" % len(arguments))
        bit_value, labels = flags(arguments[4])
        method = target_method(arguments[8])
        record = {
            "name": decode_csharp_string(arguments[1]),
            "documentation": decode_csharp_string(arguments[2]),
            "argument_names": string_array(arguments[3]),
            "flags_value": bit_value,
            "flags": labels,
            "source_start_index": int(arguments[5], 0),
            "source_end_index": int(arguments[6], 0),
            "source_path": decode_csharp_string(arguments[7]),
            "target_method": method,
            "free_variables": string_array(arguments[9]),
            "global_names": string_array(arguments[10]),
            "cell_variables": string_array(arguments[11]),
            "variable_names": string_array(arguments[12]),
            "local_count": int(arguments[13], 0),
        }
        record["source_lines"] = method_source_lines(text, method)
        record["first_source_line"] = min(record["source_lines"], default=None)
        record["last_source_line"] = max(record["source_lines"], default=None)
        key = (
            record["name"], record["source_start_index"],
            record["source_end_index"], record["source_path"], method,
        )
        recovered[key] = record
    return sorted(
        recovered.values(),
        key=lambda item: (item["source_path"] or "", item["source_start_index"], item["name"] or ""),
    )


def assembly_references(path: Path) -> list[dict[str, str]]:
    result = subprocess.run(
        ["monodis", "--assemblyref", str(path)], text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        raise RuntimeError("monodis failed for %s: %s" % (path, result.stderr))
    records = []
    version: str | None = None
    for line in result.stdout.splitlines():
        match = re.match(r"\d+: Version=(.+)", line)
        if match:
            version = match.group(1).strip()
            continue
        match = re.match(r"\s*Name=(.+)", line)
        if match and version is not None:
            records.append({"name": match.group(1).strip(), "version": version})
            version = None
    return records


def reference_class(name: str, corpus: set[str], runtime: set[str]) -> str:
    folded = name.lower()
    if folded in corpus:
        return "corpus"
    if folded in runtime:
        return "repository-runtime"
    if (
        folded in {"mscorlib", "netstandard", "system", "windowsbase",
                   "presentationcore", "presentationframework", "microsoft.csharp"}
        or folded.startswith("system.")
    ):
        return "framework"
    return "absent-from-reconstruction"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="reconstruct_eas.py output directory")
    args = parser.parse_args()
    root = args.output.resolve()
    manifest_path = root / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))

    unique: dict[str, dict[str, Any]] = {}
    for record in manifest["files"]:
        unique.setdefault(record["sha256"], record)

    function_root = root / "python-functions"
    function_root.mkdir(exist_ok=False)
    symbol_rows: list[dict[str, Any]] = []
    parse_errors: list[dict[str, str]] = []
    unknown_result_comments = 0
    ilspy_error_comments = 0

    for record in unique.values():
        source_dir = root / record["source_relative"]
        for source in source_dir.rglob("*.cs"):
            source_text = source.read_text(encoding="utf-8", errors="replace")
            unknown_result_comments += source_text.count("Unknown result type")
            ilspy_error_comments += source_text.count("Error decoding")
        if not record["dlr_cached_code"]:
            continue
        source = source_dir / "DLRCachedCode.cs"
        try:
            source_text = source.read_text(encoding="utf-8")
            functions = function_records(source_text)
        except Exception as error:
            parse_errors.append({
                "assembly_name": record["assembly_name"],
                "error": "%s: %s" % (type(error).__name__, error),
            })
            functions = []
        output = {
            "assembly_name": record["assembly_name"],
            "assembly_sha256": record["sha256"],
            "cached_modules": record["cached_modules"],
            "functions": functions,
        }
        (function_root / (record["assembly_name"] + ".json")).write_text(
            json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        for function in functions:
            symbol_rows.append({
                "assembly_name": record["assembly_name"],
                "source_path": function["source_path"],
                "name": function["name"],
                "arguments": ",".join(function["argument_names"] or []),
                "flags": ",".join(function["flags"]),
                "source_start_index": function["source_start_index"],
                "source_end_index": function["source_end_index"],
                "first_source_line": function["first_source_line"],
                "last_source_line": function["last_source_line"],
                "target_method": function["target_method"],
            })

    with (root / "python-symbols.csv").open("w", newline="", encoding="utf-8") as stream:
        fields = [
            "assembly_name", "source_path", "name", "arguments", "flags",
            "source_start_index", "source_end_index", "first_source_line",
            "last_source_line", "target_method",
        ]
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(symbol_rows)

    corpus_names = {record["assembly_name"].lower() for record in unique.values()}
    runtime_names = {
        Path(name).stem.lower()
        for name in manifest["tools"]["runtime_references_added"]
    }
    dependencies = []
    classes: dict[str, int] = {}
    absent: dict[tuple[str, str], int] = {}
    for record in unique.values():
        refs = assembly_references(Path(record["input_path"]))
        for reference in refs:
            classification = reference_class(reference["name"], corpus_names, runtime_names)
            reference["classification"] = classification
            classes[classification] = classes.get(classification, 0) + 1
            if classification == "absent-from-reconstruction":
                key = (reference["name"], reference["version"])
                absent[key] = absent.get(key, 0) + 1
        dependencies.append({
            "assembly_name": record["assembly_name"],
            "sha256": record["sha256"],
            "references": refs,
        })
    dependency_report = {
        "reference_edge_class_counts": classes,
        "absent_unique_identities": [
            {"name": name, "version": version, "referenced_by_count": count}
            for (name, version), count in sorted(absent.items())
        ],
        "assemblies": dependencies,
    }
    (root / "dependency-report.json").write_text(
        json.dumps(dependency_report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    index = {
        "cached_assemblies_indexed": sum(record["dlr_cached_code"] for record in unique.values()),
        "function_records": len(symbol_rows),
        "function_index_parse_errors": parse_errors,
        "functions_with_documentation": sum(
            1
            for path in function_root.glob("*.json")
            for function in json.loads(path.read_text(encoding="utf-8"))["functions"]
            if function["documentation"] is not None
        ),
        "csharp_unknown_result_comments": unknown_result_comments,
        "csharp_error_decoding_comments": ilspy_error_comments,
        "absent_unique_dependency_identities": len(absent),
    }
    (root / "recovery-index.json").write_text(
        json.dumps(index, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    manifest["recovery_index"] = index
    mono_version = subprocess.run(
        ["mono", "--version"], text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    ).stdout.splitlines()
    manifest["tools"]["mono"] = mono_version[0] if mono_version else "unknown"
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    readme_path = root / "README.md"
    marker = "## Python scope and dependency indexes"
    readme = readme_path.read_text(encoding="utf-8")
    if marker not in readme:
        readme += """

## Python scope and dependency indexes

- `python-functions/` and `python-symbols.csv`: {functions:,} recovered Python
  scope records, including {documents:,} retained docstrings.
- `dependency-report.json`: every AssemblyRef edge classified by availability.
- `recovery-index.json`: source-recovery coverage and decompiler diagnostics.
""".format(
            functions=index["function_records"],
            documents=index["functions_with_documentation"],
        )
        readme_path.write_text(readme, encoding="utf-8")
    print(json.dumps(index, sort_keys=True))
    return 0 if not parse_errors else 2


if __name__ == "__main__":
    raise SystemExit(main())
