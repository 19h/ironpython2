#!/usr/bin/env python3
"""Reconstruct decrypted EAS images into auditable managed-code artifacts.

The source files are preserved byte-for-byte as DLL-named mirrors.  Each unique
assembly is additionally decompiled to a C# project and, by default, to a full
ECMA-335 CIL listing.  Assemblies produced by ``clr.CompileModules`` are
inspected with the repository's IronPython runtime without executing their
module delegates.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import csv
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import struct
import subprocess
import sys
import tempfile
from typing import Any, Iterable


SCHEMA_VERSION = 1
MACHINE_NAMES = {0x014C: "I386", 0x8664: "AMD64", 0xAA64: "ARM64"}


class ReconstructionError(RuntimeError):
    pass


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read_u16(data: bytes, offset: int) -> int:
    return struct.unpack_from("<H", data, offset)[0]


def read_u32(data: bytes, offset: int) -> int:
    return struct.unpack_from("<I", data, offset)[0]


def rva_to_offset(rva: int, sections: list[dict[str, int]]) -> int:
    for section in sections:
        span = max(section["virtual_size"], section["raw_size"])
        if section["virtual_address"] <= rva < section["virtual_address"] + span:
            delta = rva - section["virtual_address"]
            if delta >= section["raw_size"]:
                raise ReconstructionError(
                    "RVA 0x%x lies in a section's zero-filled tail" % rva
                )
            return section["raw_pointer"] + delta
    raise ReconstructionError("RVA 0x%x does not map to a section" % rva)


def inspect_cli_image(path: Path) -> dict[str, Any]:
    data = path.read_bytes()
    if len(data) < 0x100:
        raise ReconstructionError("file is shorter than a PE header")
    if data[:2] != b"MZ":
        raise ReconstructionError("DOS MZ signature is absent")

    pe_offset = read_u32(data, 0x3C)
    if pe_offset + 24 > len(data) or data[pe_offset:pe_offset + 4] != b"PE\0\0":
        raise ReconstructionError("PE signature is absent or out of bounds")

    coff = pe_offset + 4
    machine = read_u16(data, coff)
    section_count = read_u16(data, coff + 2)
    optional_size = read_u16(data, coff + 16)
    optional = coff + 20
    if optional + optional_size > len(data):
        raise ReconstructionError("optional header is out of bounds")

    magic = read_u16(data, optional)
    if magic == 0x10B:
        pe_kind = "PE32"
        directory_offset = optional + 96
    elif magic == 0x20B:
        pe_kind = "PE32+"
        directory_offset = optional + 112
    else:
        raise ReconstructionError("unsupported optional-header magic 0x%x" % magic)

    cli_directory = directory_offset + 14 * 8
    if cli_directory + 8 > optional + optional_size:
        raise ReconstructionError("CLI data directory is absent")
    cli_rva = read_u32(data, cli_directory)
    cli_size = read_u32(data, cli_directory + 4)
    if cli_rva == 0 or cli_size < 72:
        raise ReconstructionError("CLI header is absent or undersized")

    section_table = optional + optional_size
    sections: list[dict[str, int]] = []
    section_names: list[str] = []
    for index in range(section_count):
        offset = section_table + index * 40
        if offset + 40 > len(data):
            raise ReconstructionError("section table is out of bounds")
        name = data[offset:offset + 8].split(b"\0", 1)[0].decode("ascii", "replace")
        section = {
            "virtual_size": read_u32(data, offset + 8),
            "virtual_address": read_u32(data, offset + 12),
            "raw_size": read_u32(data, offset + 16),
            "raw_pointer": read_u32(data, offset + 20),
        }
        if section["raw_pointer"] + section["raw_size"] > len(data):
            raise ReconstructionError("section %s raw data is out of bounds" % name)
        sections.append(section)
        section_names.append(name)

    cli_offset = rva_to_offset(cli_rva, sections)
    if cli_offset + 24 > len(data):
        raise ReconstructionError("CLI header is out of bounds")
    metadata_rva = read_u32(data, cli_offset + 8)
    metadata_size = read_u32(data, cli_offset + 12)
    cli_flags = read_u32(data, cli_offset + 16)
    metadata_offset = rva_to_offset(metadata_rva, sections)
    if metadata_offset + metadata_size > len(data):
        raise ReconstructionError("CLI metadata is out of bounds")
    if data[metadata_offset:metadata_offset + 4] != b"BSJB":
        raise ReconstructionError("CLI metadata BSJB signature is absent")

    return {
        "pe_kind": pe_kind,
        "machine": MACHINE_NAMES.get(machine, "0x%04X" % machine),
        "machine_value": machine,
        "section_count": section_count,
        "section_names": section_names,
        "cli_rva": cli_rva,
        "cli_size": cli_size,
        "cli_flags": cli_flags,
        "metadata_rva": metadata_rva,
        "metadata_size": metadata_size,
        "file_alignment_remainder": len(data) % 512,
    }


def run_checked(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, text=True, **kwargs)
    if result.returncode != 0:
        raise ReconstructionError(
            "command failed (%d): %s\n%s" %
            (result.returncode, " ".join(command), result.stderr or result.stdout)
        )
    return result


def command_version(command: list[str], env: dict[str, str] | None = None) -> str:
    result = run_checked(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env)
    return result.stdout.strip().splitlines()[0] if result.stdout.strip() else "unknown"


def detect_dotnet_root() -> str | None:
    if os.environ.get("DOTNET_ROOT"):
        return os.environ["DOTNET_ROOT"]
    result = subprocess.run(
        ["dotnet", "--info"], text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    match = re.search(r"Base Path:\s+(.+?)/sdk/[^/]+/?$", result.stdout, re.MULTILINE)
    return match.group(1) if match else None


def link_or_copy(source: Path, destination: Path) -> str:
    destination.parent.mkdir(parents=True, exist_ok=True)
    # A hardlink would initially be byte-identical, but a later write through
    # either pathname would mutate the other artifact.  Independent copies are
    # required so the reconstructed tree cannot become an alias for evidence.
    shutil.copy2(source, destination)
    return "copy"


def cached_code_metadata(
    ipy: Path, helper: Path, paths: Iterable[Path], env: dict[str, str]
) -> dict[str, dict[str, Any]]:
    input_text = "".join(str(path.resolve()) + "\n" for path in paths)
    result = subprocess.run(
        [str(ipy), str(helper)], input=input_text, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env,
    )
    if result.returncode != 0:
        raise ReconstructionError(
            "cached-code reflector failed (%d): %s" %
            (result.returncode, result.stderr)
        )

    records: dict[str, dict[str, Any]] = {}
    for line_number, line in enumerate(result.stdout.splitlines(), 1):
        try:
            record = json.loads(line)
        except json.JSONDecodeError as error:
            raise ReconstructionError(
                "invalid reflector JSON on line %d: %s" % (line_number, error)
            ) from error
        records[str(Path(record["path"]).resolve())] = record
    return records


def decompile_one(
    item: dict[str, Any], ilspy: Path, references: Path, source_root: Path,
    il_root: Path | None, log_root: Path, env: dict[str, str]
) -> dict[str, Any]:
    source_path = Path(item["input_path"])
    safe_name = item["assembly_name"]
    project_dir = source_root / safe_name
    project_dir.mkdir(parents=True, exist_ok=False)
    log_path = log_root / (safe_name + ".log")

    command = [
        str(ilspy), "--disable-updatecheck", "--nested-directories", "-p",
        "-o", str(project_dir), "-r", str(references), str(source_path),
    ]
    result = subprocess.run(
        command, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env,
    )
    log_path.write_text(
        "COMMAND\n%s\n\nSTDOUT\n%s\nSTDERR\n%s" %
        (" ".join(command), result.stdout, result.stderr),
        encoding="utf-8",
    )
    if result.returncode != 0:
        return {
            "assembly_name": safe_name,
            "decompile_ok": False,
            "decompile_error": result.stderr.strip() or result.stdout.strip(),
            "source_file_count": 0,
            "project_file": None,
            "cil_ok": False if il_root is not None else None,
            "cil_file": None,
            "cil_error": None,
        }

    source_files = list(project_dir.rglob("*.cs"))
    projects = list(project_dir.glob("*.csproj"))
    decompile_ok = bool(source_files and projects)

    cil_ok: bool | None = None
    cil_relative: str | None = None
    cil_error: str | None = None
    if il_root is not None:
        cil_path = il_root / (safe_name + ".il")
        il_command = [
            str(ilspy), "--disable-updatecheck", "-il", "-r", str(references),
            str(source_path),
        ]
        with cil_path.open("w", encoding="utf-8") as cil_stream:
            il_result = subprocess.run(
                il_command, text=True, stdout=cil_stream,
                stderr=subprocess.PIPE, env=env,
            )
        cil_ok = il_result.returncode == 0 and cil_path.stat().st_size > 0
        cil_error = None if cil_ok else il_result.stderr.strip()
        cil_relative = str(cil_path)

    return {
        "assembly_name": safe_name,
        "decompile_ok": decompile_ok,
        "decompile_error": None if decompile_ok else "project or C# output is absent",
        "source_file_count": len(source_files),
        "project_file": str(projects[0]) if projects else None,
        "cil_ok": cil_ok,
        "cil_file": cil_relative,
        "cil_error": cil_error,
    }


def write_readme(output: Path, manifest: dict[str, Any]) -> None:
    counts = manifest["counts"]
    text = """# Reconstructed EAS corpus

This directory was generated without modifying the source corpus.

## Artifact layers

- `assemblies/`: all {files} inputs mirrored as hash-identical `.dll` files.
- `references/`: one collision-checked DLL per assembly name, plus the local
  IronPython 2.7.12 runtime used for dependency-aware analysis.
- `source/`: ILSpy C# project-shaped decompilation for each of the {unique}
  unique assemblies.
- `cil/`: ECMA-335 CIL listings for each unique assembly.
- `python-metadata/`: non-executing cached-code metadata for assemblies emitted
  by IronPython `clr.CompileModules`.
- `logs/`: complete per-assembly decompiler command/output records.
- `manifest.json` and `manifest.csv`: hashes, PE/CLI facts, duplicate mappings,
  classifications, and validation results.

## Recovery boundary

The DLL mirrors are lossless: each SHA-256 digest equals its corresponding EAS
input.  C# and CIL outputs recover executable semantics and metadata but are not
the original source text.  For IronPython cached-code assemblies, comments,
formatting, and some high-level syntactic choices were not serialized by the
compiler and cannot be recovered exactly.  Surviving Python-level module names,
source paths, global names, delegate names, and metadata tokens are recorded.

## Counts

- Input files: {files}
- Unique SHA-256 values: {unique}
- Duplicate instances: {duplicates}
- IronPython cached-code assemblies: {cached}
- Conventional or mixed CLI assemblies: {conventional}
- Successful C# decompilations: {decompiled}
- Successful CIL listings: {cil}
""".format(
        files=counts["input_files"], unique=counts["unique_sha256"],
        duplicates=counts["duplicate_instances"], cached=counts["dlr_cached_code"],
        conventional=counts["unique_sha256"] - counts["dlr_cached_code"],
        decompiled=counts["decompile_success"], cil=counts["cil_success"],
    )
    (output / "README.md").write_text(text, encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="root containing decrypted .eas files")
    parser.add_argument("output", type=Path, help="new output directory")
    parser.add_argument("--ilspy", type=Path, required=True, help="path to ilspycmd")
    parser.add_argument("--ipy", type=Path, required=True, help="repository-built ipy executable")
    parser.add_argument("--jobs", type=int, default=max(1, min(4, (os.cpu_count() or 2) // 2)))
    parser.add_argument("--no-cil", action="store_true", help="omit exact CIL listings")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    input_root = args.input.resolve()
    output = args.output.resolve()
    ilspy = args.ilspy.resolve()
    ipy = args.ipy.resolve()
    helper = Path(__file__).with_name("eas_cached_code_metadata.py").resolve()

    if not input_root.is_dir():
        raise ReconstructionError("input directory does not exist: %s" % input_root)
    if output.exists():
        raise ReconstructionError("output path already exists: %s" % output)
    if not ilspy.is_file() or not ipy.is_file() or not helper.is_file():
        raise ReconstructionError("ilspy, ipy, or cached-code helper is absent")
    if args.jobs < 1:
        raise ReconstructionError("--jobs must be positive")

    eas_paths = sorted(input_root.rglob("*.eas"), key=lambda p: str(p).lower())
    if not eas_paths:
        raise ReconstructionError("no .eas files found under %s" % input_root)

    output.mkdir(parents=True)
    assemblies_root = output / "assemblies"
    references_root = output / "references"
    source_root = output / "source"
    il_root = None if args.no_cil else output / "cil"
    metadata_root = output / "python-metadata"
    log_root = output / "logs" / "decompile"
    for directory in (assemblies_root, references_root, source_root, metadata_root, log_root):
        directory.mkdir(parents=True, exist_ok=True)
    if il_root is not None:
        il_root.mkdir(parents=True)

    dotnet_root = detect_dotnet_root()
    env = os.environ.copy()
    if dotnet_root:
        env["DOTNET_ROOT"] = dotnet_root

    records: list[dict[str, Any]] = []
    by_hash: dict[str, list[dict[str, Any]]] = {}
    for index, path in enumerate(eas_paths, 1):
        relative = path.relative_to(input_root)
        digest = sha256_file(path)
        cli = inspect_cli_image(path)
        dll_relative = relative.with_suffix(".dll")
        dll_path = assemblies_root / dll_relative
        transfer = link_or_copy(path, dll_path)
        if sha256_file(dll_path) != digest:
            raise ReconstructionError("hash mismatch after mirroring %s" % relative)
        record = {
            "input_index": index,
            "relative_eas": str(relative),
            "input_path": str(path.resolve()),
            "size_bytes": path.stat().st_size,
            "sha256": digest,
            "dll_relative": str(Path("assemblies") / dll_relative),
            "mirror_method": transfer,
            "mirror_hash_verified": True,
            **cli,
        }
        records.append(record)
        by_hash.setdefault(digest, []).append(record)

    basename_hashes: dict[str, set[str]] = {}
    for record in records:
        key = Path(record["relative_eas"]).name.lower()
        basename_hashes.setdefault(key, set()).add(record["sha256"])
    collisions = {key: values for key, values in basename_hashes.items() if len(values) > 1}
    if collisions:
        raise ReconstructionError("same assembly basename has distinct content: %r" % collisions)

    unique_records: list[dict[str, Any]] = []
    for digest, group in sorted(by_hash.items(), key=lambda pair: pair[1][0]["relative_eas"].lower()):
        canonical = group[0]
        canonical["duplicate_of"] = None
        unique_records.append(canonical)
        for duplicate in group[1:]:
            duplicate["duplicate_of"] = canonical["relative_eas"]

    reflection = cached_code_metadata(
        ipy, helper, (Path(record["input_path"]) for record in unique_records), env
    )
    if len(reflection) != len(unique_records):
        raise ReconstructionError("reflector result cardinality mismatch")
    for record in unique_records:
        metadata = reflection[str(Path(record["input_path"]).resolve())]
        record.update({
            "reflection_ok": metadata["reflection_ok"],
            "reflection_error": metadata["error"],
            "assembly_full_name": metadata["assembly_full_name"],
            "assembly_name": metadata["assembly_name"],
            "assembly_version": metadata["assembly_version"],
            "dlr_cached_code": metadata["dlr_cached_code"],
            "cached_languages": metadata["cached_languages"],
            "cached_modules": metadata["cached_modules"],
        })
        if not metadata["reflection_ok"]:
            raise ReconstructionError(
                "reflection failed for %s: %s" %
                (record["relative_eas"], metadata["error"])
            )
        expected_name = Path(record["relative_eas"]).stem
        if record["assembly_name"].lower() != expected_name.lower():
            raise ReconstructionError(
                "assembly/file name mismatch: %s != %s" %
                (record["assembly_name"], expected_name)
            )

    unique_by_hash = {record["sha256"]: record for record in unique_records}
    for record in records:
        canonical = unique_by_hash[record["sha256"]]
        for key in (
            "reflection_ok", "reflection_error", "assembly_full_name", "assembly_name",
            "assembly_version", "dlr_cached_code", "cached_languages", "cached_modules",
        ):
            record[key] = canonical[key]

    # All basenames are collision-free, so this directory can be used directly
    # as ILSpy's assembly search path.
    for record in unique_records:
        source = assemblies_root / Path(record["dll_relative"]).relative_to("assemblies")
        destination = references_root / (record["assembly_name"] + ".dll")
        link_or_copy(source, destination)

    runtime_dir = ipy.parent
    runtime_references = []
    for name in ("IronPython.dll", "IronPython.Modules.dll", "Microsoft.Dynamic.dll", "Microsoft.Scripting.dll"):
        candidate = runtime_dir / name
        if candidate.is_file() and not (references_root / name).exists():
            link_or_copy(candidate, references_root / name)
            runtime_references.append(name)

    for record in unique_records:
        if record["dlr_cached_code"]:
            metadata_path = metadata_root / (record["assembly_name"] + ".json")
            metadata_path.write_text(
                json.dumps({
                    "assembly_name": record["assembly_name"],
                    "assembly_version": record["assembly_version"],
                    "sha256": record["sha256"],
                    "cached_languages": record["cached_languages"],
                    "cached_modules": record["cached_modules"],
                }, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            record["python_metadata_relative"] = str(
                Path("python-metadata") / metadata_path.name
            )
        else:
            record["python_metadata_relative"] = None

    # Larger assemblies start first so failures and peak resource use are seen
    # early.  Each subprocess is independent and writes to a unique directory.
    work = sorted(unique_records, key=lambda record: -record["size_bytes"])
    results: dict[str, dict[str, Any]] = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = {
            executor.submit(
                decompile_one, record, ilspy, references_root, source_root,
                il_root, log_root, env,
            ): record
            for record in work
        }
        completed = 0
        for future in concurrent.futures.as_completed(futures):
            record = futures[future]
            try:
                result = future.result()
            except Exception as error:
                result = {
                    "assembly_name": record["assembly_name"],
                    "decompile_ok": False,
                    "decompile_error": "%s: %s" % (type(error).__name__, error),
                    "source_file_count": 0,
                    "project_file": None,
                    "cil_ok": False if il_root is not None else None,
                    "cil_file": None,
                    "cil_error": None,
                }
            results[record["sha256"]] = result
            completed += 1
            if completed == 1 or completed % 25 == 0 or completed == len(work):
                print("decompiled %d/%d" % (completed, len(work)), flush=True)

    for record in unique_records:
        result = results[record["sha256"]]
        record.update(result)
        record["source_relative"] = str(Path("source") / record["assembly_name"])
        if result["project_file"]:
            record["project_file"] = str(
                Path(result["project_file"]).resolve().relative_to(output)
            )
        if result.get("cil_file"):
            record["cil_file"] = str(
                Path(result["cil_file"]).resolve().relative_to(output)
            )

    for record in records:
        canonical = unique_by_hash[record["sha256"]]
        for key in (
            "decompile_ok", "decompile_error", "source_file_count", "project_file",
            "source_relative", "cil_ok", "cil_file", "cil_error",
            "python_metadata_relative",
        ):
            record[key] = canonical.get(key)

    decompile_failures = [record for record in unique_records if not record["decompile_ok"]]
    cil_failures = [
        record for record in unique_records
        if il_root is not None and not record["cil_ok"]
    ]
    counts = {
        "input_files": len(records),
        "input_bytes": sum(record["size_bytes"] for record in records),
        "unique_sha256": len(unique_records),
        "duplicate_groups": sum(len(group) > 1 for group in by_hash.values()),
        "duplicate_instances": len(records) - len(unique_records),
        "pe32": sum(record["pe_kind"] == "PE32" for record in records),
        "pe32_plus": sum(record["pe_kind"] == "PE32+" for record in records),
        "dlr_cached_code": sum(record["dlr_cached_code"] for record in unique_records),
        "cached_modules": sum(len(record["cached_modules"]) for record in unique_records),
        "reflection_success": sum(record["reflection_ok"] for record in unique_records),
        "decompile_success": len(unique_records) - len(decompile_failures),
        "cil_success": 0 if il_root is None else len(unique_records) - len(cil_failures),
    }

    manifest = {
        "schema_version": SCHEMA_VERSION,
        "generated_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "input_root": str(input_root),
        "output_root": str(output),
        "tools": {
            "python": sys.version.splitlines()[0],
            "ilspy": command_version([str(ilspy), "-v"], env),
            "ironpython": command_version([str(ipy), "-V"], env),
            "dotnet_root": dotnet_root,
            "runtime_references_added": runtime_references,
        },
        "counts": counts,
        "validation": {
            "all_inputs_are_bounded_cli_images": True,
            "all_mirror_hashes_match": all(record["mirror_hash_verified"] for record in records),
            "all_mirrors_inode_independent": True,
            "basename_hash_collisions": 0,
            "all_unique_assemblies_reflect": not any(not record["reflection_ok"] for record in unique_records),
            "decompile_failures": [record["relative_eas"] for record in decompile_failures],
            "cil_failures": [record["relative_eas"] for record in cil_failures],
        },
        "files": records,
    }

    (output / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    with (output / "manifest.csv").open("w", newline="", encoding="utf-8") as stream:
        fieldnames = [
            "relative_eas", "size_bytes", "sha256", "duplicate_of", "dll_relative",
            "pe_kind", "machine", "assembly_name", "assembly_version",
            "dlr_cached_code", "reflection_ok", "decompile_ok", "cil_ok",
            "source_relative", "python_metadata_relative",
        ]
        writer = csv.DictWriter(stream, fieldnames=fieldnames, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(records)
    write_readme(output, manifest)

    print(json.dumps(counts, sort_keys=True))
    if decompile_failures or cil_failures:
        return 2
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ReconstructionError as error:
        print("error: %s" % error, file=sys.stderr)
        raise SystemExit(1)
