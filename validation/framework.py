#!/usr/bin/env python3
"""Reproducible decoder validation without publication approval state."""

from __future__ import annotations

import copy
import hashlib
import json
import math
import os
import queue
import re
import selectors
import shutil
import struct
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path
from typing import Any, BinaryIO
from urllib.parse import urlsplit

try:
    from jsonschema import Draft202012Validator, FormatChecker, ValidationError
except ImportError as error:
    raise RuntimeError(
        "schema validation requires validation/requirements.txt"
    ) from error

try:
    import resource
except ImportError:  # pragma: no cover - unavailable on Windows
    resource = None

ROOT = Path(__file__).resolve().parents[1]
VALIDATION = ROOT / "validation"
CORPUS_DIR = VALIDATION / "generated" / "corpus"
RESULTS_DIR = ROOT / "target" / "validation"
MANIFEST_PATH = VALIDATION / "corpus.json"
PROFILE_ID = "jpeg2000-rs-first-release-proposed"
GENERATOR_ID = "jpeg2000-rs-validation-generator-v1"
OFFICIAL_VECTOR_ROOT_ENV = "JPEG2000_OFFICIAL_VECTOR_ROOT"
OFFICIAL_VECTOR_MANIFEST_ENV = "JPEG2000_OFFICIAL_VECTOR_MANIFEST"
FORMAT_CHECKER = FormatChecker()


@FORMAT_CHECKER.checks("date-time", raises=ValueError)
def _date_time_format(value: Any) -> bool:
    if not isinstance(value, str):
        return True
    if not re.fullmatch(
        r"\d{4}-\d{2}-\d{2}[Tt]\d{2}:\d{2}:\d{2}(?:\.\d+)?(?:[Zz]|[+-]\d{2}:\d{2})",
        value,
    ):
        return False
    return datetime.fromisoformat(value.upper().replace("Z", "+00:00")).tzinfo is not None


@FORMAT_CHECKER.checks("uri", raises=ValueError)
def _uri_format(value: Any) -> bool:
    if not isinstance(value, str):
        return True
    parsed = urlsplit(value)
    return (
        bool(parsed.scheme)
        and not any(character.isspace() for character in value)
        and (parsed.scheme not in ("http", "https") or bool(parsed.netloc))
    )


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(json.dumps(value, indent=2, sort_keys=True).encode() + b"\n")


@lru_cache(maxsize=32)
def _checked_schema(schema_text: str) -> Draft202012Validator:
    schema = json.loads(schema_text)
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema, format_checker=FORMAT_CHECKER)


def validate_schema(schema_path: Path, value: Any) -> None:
    validator = _checked_schema(schema_path.read_text(encoding="utf-8"))
    try:
        validator.validate(value)
    except ValidationError as error:
        raise ValueError(f"{schema_path.name}: {error.message}") from error
    if isinstance(value, dict) and "provenance" in value:
        validate_schema(VALIDATION / "run-provenance.schema.json", value["provenance"])


def source_binding(source_root: Path | None = None) -> dict[str, Any]:
    """Describe this run's checkout, not a reusable approval or source snapshot."""
    root = source_root or ROOT
    paths = [
        path
        for directory in ("src", "specs", "proofs", "examples")
        for path in (root / directory).rglob("*.rs")
    ]
    paths.extend(
        root / name
        for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml")
        if (root / name).is_file()
    )
    hashes = {
        path.relative_to(root).as_posix(): sha256_file(path)
        for path in sorted(paths)
    }
    tools = {
        path.relative_to(ROOT).as_posix(): sha256_file(path)
        for path in sorted(
            list(VALIDATION.glob("*.py"))
            + list(VALIDATION.glob("*.sh"))
            + list(VALIDATION.glob("*.schema.json"))
            + [VALIDATION / "requirements.txt"]
        )
    }
    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=root, capture_output=True, check=True,
        text=True,
    ).stdout.strip()
    dirty = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=normal"],
        cwd=root, capture_output=True, check=True, text=True,
    ).stdout
    return {
        "git_commit": commit,
        "git_dirty": bool(dirty),
        "source_revision": "sha256-tree-v1:" + sha256_bytes(canonical_bytes(hashes)),
        "source_hashes": hashes,
        "tool_hashes": tools,
        "python": sys.version.split()[0],
    }


def report_path(output_dir: Path | None, name: str) -> Path:
    path = ((output_dir or RESULTS_DIR) / name).resolve()
    try:
        relative = path.relative_to(ROOT)
    except ValueError:
        return path
    tracked = subprocess.run(
        ["git", "ls-files", "--error-unmatch", "--", relative.as_posix()],
        cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False,
    )
    if tracked.returncode == 0:
        raise ValueError(f"refusing to overwrite tracked report: {relative}")
    return path


def report_schema(output_dir: Path | None, name: str) -> str:
    return os.path.relpath(VALIDATION / name, (output_dir or RESULTS_DIR).resolve())


def validate_evidence_schemas(output_dir: Path | None = None) -> dict[str, Any]:
    """Check static inputs and any reports present; absent reports are not passes."""
    checked = []
    for path in sorted(VALIDATION.glob("*.schema.json")):
        Draft202012Validator.check_schema(json.loads(path.read_text()))
        checked.append(path.name)
    for schema, instance in (
        ("corpus.schema.json", MANIFEST_PATH),
        ("oracle-config.schema.json", VALIDATION / "oracles.json"),
    ):
        validate_schema(VALIDATION / schema, json.loads(instance.read_text()))
    validate_normative_coverage()
    reports = []
    for name, schema in (
        ("validation-results.json", "validation-result.schema.json"),
        ("budget-results.json", "budget-result.schema.json"),
        ("oracle-adjudications.json", "oracle-adjudication.schema.json"),
        ("official-vector-results.json", "official-vector-result.schema.json"),
        ("proof-coverage.json", "proof-coverage.schema.json"),
        ("numerical-results.json", "numerical-result.schema.json"),
        ("htj2k-results.json", "numerical-result.schema.json"),
        ("resource-results.json", "resource-result.schema.json"),
    ):
        path = (output_dir or RESULTS_DIR) / name
        if path.is_file():
            validate_schema(VALIDATION / schema, json.loads(path.read_text()))
            reports.append(name)
    return {"status": "passed", "schemas": checked, "reports": reports}


def _coverage_symbol_present(path: Path, symbol: str, *, text: str | None = None) -> bool:
    short = re.escape(symbol.rsplit("::", 1)[-1])
    return bool(re.search(
        rf"\b(?:fn|struct|enum|type|const|trait)\s+{short}\b",
        text if text is not None else path.read_text(encoding="utf-8"),
    ))


def _coverage_function_header(
    text: str, symbol: str, *,
    implementation_ranges: dict[tuple[str, str, str], list[tuple[int, int, str]] | None] | None = None,
    module_scope: bool = False,
) -> re.Match[str] | None:
    """Resolve formatted methods in their actual impl, never another short name."""
    short = symbol.rsplit("::", 1)[-1]
    pattern = re.compile(
        rf"(?m)^([ \t]*)(?:(?:pub(?:\([^)\n]*\))?|const|async|unsafe)[ \t]+)*"
        rf"fn[ \t]+{re.escape(short)}\b",
    )
    if module_scope:
        matches = [match for match in pattern.finditer(text) if not match[1]]
        if len(matches) != 1:
            return None
        match = matches[0]
        prefix = text[text.rfind("\n}", 0, match.start()) + 2:match.start()]
        return None if re.search(r"#\[\s*cfg\s*\(\s*any\s*\(\s*\)\s*\)\s*\]", prefix) else match
    if "::" in symbol:
        owner = symbol.rsplit("::", 1)[0].rsplit("::", 1)[-1]
        trait_scope = (
            r"(?:Tier1SymbolDecoder[ \t]+for[ \t]+)?"
            if symbol == "RawBitReader::decode" else ""
        )
        if short == "clone":
            trait_scope = r"(?:Clone[ \t]+for[ \t]+)?"
        if symbol == "JpipByteView::as_ref":
            trait_scope = r"AsRef[ \t]*<[ \t]*\[[ \t]*u8[ \t]*\][ \t]*>[ \t]+for[ \t]+"
        if implementation_ranges is None:
            implementation_ranges = {}
        key = (text, owner, trait_scope)
        if key not in implementation_ranges:
            ranges = []
            for implementation in re.finditer(
                rf"(?m)^([ \t]*)impl(?:[ \t]*<[^{{}}\n]*>)?[ \t]+"
                rf"{trait_scope}{re.escape(owner)}\b(?![^{{}}\n]*\bfor\b)[^{{}}\n]*\{{", text,
            ):
                closing = re.search(
                    rf"(?m)^{re.escape(implementation[1])}\}}[ \t]*(?://[^\n]*)?$",
                    text[implementation.end():],
                )
                if closing is None:
                    implementation_ranges[key] = None
                    break
                start = implementation.end()
                ranges.append((start, start + closing.start(), implementation[1]))
            else:
                implementation_ranges[key] = ranges
        resolved_ranges = implementation_ranges[key]
        if resolved_ranges is None:
            return None
        matches = []
        for start, end, indentation in resolved_ranges:
            matches.extend(
                match for match in pattern.finditer(text, start, end)
                if match[1] == indentation + "    "
            )
        return matches[0] if len(matches) == 1 else None
    return pattern.search(text)


def _coverage_function_body(text: str, header: re.Match[str] | None) -> str | None:
    if header is None:
        return None
    body_start = text.find("{", header.end())
    if body_start < 0:
        return None
    closing = re.search(
        rf"(?m)^{re.escape(header[1])}\}}[ \t]*(?://[^\n]*)?$", text[body_start + 1:],
    )
    if closing is None:
        return None
    return text[body_start + 1:body_start + 1 + closing.start()]


def _coverage_spec_function_body(text: str, symbol: str) -> str | None:
    headers = list(re.finditer(
        r"(?m)^([ \t]*)pub(?:\((?:crate|super)\))?[ \t]+(?:open|closed)[ \t]+spec[ \t]+fn[ \t]+"
        + re.escape(symbol) + r"\b", text,
    ))
    return _coverage_function_body(text, headers[0]) if len(headers) == 1 else None


def _coverage_same_file_call(
    text: str, caller: str, callee: str, *, distinct_file: bool = False, module_scope: bool = False,
) -> bool:
    """Check another formatted function body, not the callee declaration."""
    same_name = caller.rsplit("::", 1)[-1] == callee
    if same_name and not distinct_file:
        return False
    body = _coverage_function_body(text, _coverage_function_header(text, caller, module_scope=module_scope))
    prefix = r"(?<![\w.])" if same_name else r"\b"
    return body is not None and re.search(rf"{prefix}{re.escape(callee)}\s*\(", body) is not None


def _coverage_definition_path(parent: str, symbol: str) -> str:
    root = ROOT / parent
    directory = root.parent / root.stem
    candidates = [root]
    parent_text = root.read_text(encoding="utf-8")
    for path in sorted(directory.glob("*.rs")):
        if path.name in {"tests.rs", "proof_support.rs"}:
            continue
        if re.search(rf"(?m)^\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+{re.escape(path.stem)}\s*;", parent_text):
            candidates.append(path)
    matches = [
        path for path in candidates
        if _coverage_function_header(path.read_text(encoding="utf-8"), symbol) is not None
    ]
    if len(matches) != 1:
        raise ValueError(f"expected exactly one executing definition for {parent}::{symbol}")
    return matches[0].relative_to(ROOT).as_posix()


def _coverage_named_caller_required(path: str) -> bool:
    return path == "src/tier1.rs" or (path.startswith("src/") and path.count("/") > 1)


def _coverage_result_arguments(
    contract: str,
    result: re.Match[str] | None,
    model: str,
    arguments: str,
) -> bool:
    if result is None or result["model"] != model:
        return False
    # Bind this returned-result clause, not a later occurrence of the model.
    return re.match(r"\s*" + arguments + r"\s*,?\s*\)", contract[result.end():]) is not None


def _coverage_call(name: str, *arguments: str) -> str:
    return re.escape(name) + r"\s*\(\s*" + r"\s*,\s*".join(arguments) + r"\s*\)"

def _coverage_body_clause(text: str) -> str:
    statement = text.split(";", 1)[0] + ";"
    normalized = re.sub(r",(?=\))", "", "".join(statement.split()))
    return normalized.replace("|{", "|", 1).replace("});", ");", 1)

def _coverage_verified_body_clause(text: str, header: re.Match[str] | None, symbol: str, clause: str) -> bool:
    if header is None:
        return False
    body = _coverage_function_body(text, header)
    owner = symbol.split("::")[0]
    verified_impls = re.finditer(
        r"#\[\s*cfg_attr\(\s*verus_keep_ghost\s*,\s*verus_verify\s*\)\s*\]\s*impl\s+" + re.escape(owner) + r"\s*\{", text,
    )
    verified_owner = False
    for implementation in verified_impls:
        closing = re.search(r"(?m)^\}[ \t]*$", text[implementation.end():])
        if closing is not None and implementation.end() <= header.start() < implementation.end() + closing.start():
            verified_owner = True
            break
    return (verified_owner and body is not None
            and _coverage_body_clause(body) == _coverage_body_clause("#[cfg(verus_keep_ghost)]" + clause)
            and re.search(r"\b(?:requires|assume|admit|external_body)\b", body) is None)


def _packet_header_contracts() -> dict[tuple[str, str], tuple[str, str, str | None, str]]:
    def old(name: str) -> str:
        return _coverage_call("old", re.escape(name))

    def final(name: str) -> str:
        return _coverage_call("final", re.escape(name))

    def view(name: str, *values: str) -> str:
        return _coverage_call(name, *values)

    def arguments(*values: str) -> str:
        return r"\s*,\s*".join(values)

    def cap(name: str) -> str:
        return _coverage_call("crate::limits::resource_" + name + "_limit", "limits")

    def reader(value: str) -> str:
        return view("packet_bit_reader_view", value)

    def packet(value: str) -> str:
        return view("code_block_packet_state_view", value)

    def tree(value: str) -> str:
        return view("tag_tree_view", value)

    def segments(value: str) -> str:
        return view("header_segments_view", value)

    state_reader = arguments(packet(final("state")), reader(final("reader")))
    full_header = arguments(packet(final("state")), tree(final("inclusion_tree")),
                            tree(final("zero_bitplane_tree")), reader(final("reader")))
    old_header = arguments(packet(old("state")), tree(old("inclusion_tree")),
                           tree(old("zero_bitplane_tree")))
    segment_state = arguments(packet(final("state")), segments(final("segments")), reader(final("reader")))
    segment_old = arguments(packet(old("state")), segments(old("segments")), reader(old("reader")))
    body_caps = arguments(cap("code_block_pass"), cap("code_block_byte"), cap("input_byte"), cap("work"))
    precinct_caps = arguments(cap("packet_header_byte"), body_caps)
    precinct_old = view("packet_precinct_view", old("precinct"))
    precinct_final = view("packet_precinct_view", final("precinct"))
    parameters = view("precinct_payload_parameters_view", "parameters")
    association_final = view("precinct_header_view", *(final(name) for name in (
        "states", "subbands", "contributions", "reader", "progress",
    )))
    association_old = view("precinct_header_view", *(old(name) for name in (
        "states", "subbands", "contributions", "reader", "progress",
    )))
    packet_contracts = {
        "packet_reader_error": ("part1_packet_reader_error", r"\1", None, arguments("offset", "kind")),
        "packet_reader_limit": ("part1_packet_reader_limit", r"\1", None, arguments("resource", "limit", "actual")),
        "packet_reader_prefix_from_input": (
            "part1_packet_reader_prefix", reader(r"&\s*\1"), None, arguments("input@", "header_limit", "work_limit")),
        "packet_reader_from_input": (
            "part1_packet_reader_initial", view("packet_reader_outcome", r"\1"), None,
            arguments("input@", "header_limit", "work_limit")),
        "packet_reader_new": (
            "part1_packet_reader_initial", view("packet_reader_outcome", r"\1"), None,
            arguments("input@", cap("packet_header_byte"), cap("work"))),
        "packet_reader_prefix": (
            "part1_packet_reader_prefix", reader(r"&\s*\1"), None,
            arguments("input@", cap("packet_header_byte"), cap("work"))),
        "PacketBitReader::read_bit": (
            "part1_packet_reader_read", r"\1", reader(final("self")), reader(old("self"))),
        "PacketBitReader::read_bits": (
            "part1_packet_reader_read_bits", r"\1", reader(final("self")), arguments(reader(old("self")), "count")),
        "PacketBitReader::load_byte": (
            "part1_packet_reader_load", r"\1", reader(final("self")), reader(old("self"))),
        "PacketBitReader::finish_packet_header": (
            "part1_packet_reader_finish", r"\1", reader(final("self")), reader(old("self"))),
        "code_block_packet_state_new": (
            "part1_code_block_packet_initial", packet(r"&\s*\1"), None, ""),
        "header_segments_new": (
            "part1_header_segments_initial", segments(r"&\s*\1"), None, arguments(packet("state"), "style")),
        "read_header_segment_length": (
            "part1_header_segment_length", r"\1", segment_state,
            arguments(segment_old, "first_pass", "remaining_passes", "passes", "length_bits")),
        "read_header_prefix": (
            "part1_header_prefix", r"\1", full_header, arguments(old_header, "context", reader(old("reader")))),
        "decode_code_block_contribution": (
            "part1_packet_header_decode", view("code_block_header_outcome", r"\1"), full_header,
            arguments(old_header, "context", reader(old("reader")))),
        "read_header_segments": (
            "part1_header_segments", view("header_segments_outcome", r"\1"), state_reader,
            arguments(packet(old("state")), reader(old("reader")), "new_passes", "context")),
        "read_header_segment": (
            "part1_header_segment_step", r"\1", segment_state,
            arguments(segment_old, "new_passes", "context")),
        "commit_header_contribution": (
            "part1_header_commit", view("code_block_header_outcome", r"\1"), packet(final("state")),
            arguments(packet(old("state")), packet(r"&\s*next_state"), segments(r"&\s*segments"),
                      "first_inclusion", "new_passes", reader("reader"))),
        "read_header_zero_bitplanes": (
            "part1_header_zero_loop", r"\1",
            arguments(packet(final("state")), tree(final("tree")), reader(final("reader"))),
            arguments(packet(old("state")), tree(old("tree")), "context", reader(old("reader")), "1")),
        "read_new_passes": (
            "part1_header_new_passes", r"\1", reader(final("reader")), reader(old("reader"))),
        "read_header_lblock": (
            "part1_header_lblock", r"\1", state_reader,
            arguments(packet(old("state")), reader(old("reader")), "32")),
        "floor_log2": ("part1_header_floor_log2", r"\1", None, "value"),
        "TagTree::leaf_count": ("part1_tag_leaf_count", r"\1", None, tree("self")),
        "TagTree::decode_path": (
            "part1_tag_path", view("tag_path_outcome", r"\1"), None,
            arguments(tree("self"), "leaf_x", "leaf_y", "error_offset")),
        "TagTree::decode_path_nodes": (
            "part1_tag_reverse", r"\1", arguments(tree(final("self")), reader(final("reader"))),
            arguments(tree(old("self")), view("tag_path_view", "path"), r"path\.length\s+as\s+nat",
                      "0", "threshold", reader(old("reader")))),
        "TagTree::decode": (
            "part1_tag_tree_decode", r"\1", arguments(tree(final("self")), reader(final("reader"))),
            arguments(tree(old("self")), "leaf_x", "leaf_y", "threshold", reader(old("reader")))),
        "decode_tag_tree_node": (
            "part1_tag_node_decode", r"\1",
            arguments(view("tag_node_view", r"\*\s*" + final("node")), reader(final("reader"))),
            arguments(view("tag_node_view", r"\*\s*" + old("node")), "inherited", "threshold", reader(old("reader")))),
        "tag_tree_new": (
            "part1_tag_initial", view("tag_tree_outcome", r"\1"), None,
            arguments("width", "height", cap("tag_tree_node"))),
        "tag_tree_from_dimensions": (
            "part1_tag_initial", view("tag_tree_outcome", r"\1"), None,
            arguments("width", "height", "maximum_nodes")),
        "decode_precinct_header_slot": (
            "part1_precinct_header_slot", r"\1", association_final,
            arguments(association_old, "contexts@", r"parameters\.layer", r"parameters\.style")),
        "decode_precinct_header_members": (
            "part1_precinct_header_members", r"\1", association_final,
            arguments(association_old, "contexts@", r"parameters\.0\.layer", r"parameters\.0\.style", r"parameters\.1")),
        "decode_precinct_contribution_headers": (
            "part1_precinct_headers", r"\1", association_final,
            arguments(association_old, "contexts@", r"parameters\.layer", r"parameters\.style")),
        "decode_precinct_packet": (
            "part1_precinct_packet", r"\1", precinct_final,
            arguments(precinct_old, "tile_part", "offset", "packed_headers@", "packed_offset",
                      "expected_packet_length", "expected_sop_sequence", "decode_tier1", cap("code_block"), precinct_caps)),
        "decode_precinct_packet_payload_prefix": (
            "part1_precinct_payload_prefix", view("precinct_payload_reader_outcome", r"\1"), None,
            arguments("data@", "packed_headers@", parameters, cap("packet_header_byte"), cap("work"))),
        "decode_precinct_packet_payload": (
            "part1_precinct_payload", r"\1", precinct_final,
            arguments(precinct_old, "data@", "packed_headers@", parameters, precinct_caps)),
        "decode_precinct_packet_payload_after_headers": (
            "part1_precinct_payload_after_headers", r"\1", precinct_final,
            arguments(precinct_old, parameters, "data@",
                      view("precinct_payload_header_view", "header") + r"\.0\.packet_data",
                      view("precinct_payload_header_view", "header") + r"\.0\.reader",
                      view("precinct_payload_header_view", "header") + r"\.1",
                      view("precinct_payload_header_view", "header") + r"\.2",
                      view("precinct_payload_header_view", "header") + r"\.0\.present",
                      view("precinct_payload_header_view", "header") + r"\.0\.sop_bytes", body_caps)),
    }
    tier1_contracts = {
        "Tier1CodeBlockDecoder::admit_legacy_contribution": (
            "part1_legacy_contribution_admission", r"\1", view("tier1_decoder_state", final("self")),
            arguments(view("tier1_decoder_state", old("self")), "input@", "passes", cap("code_block_byte"), cap("work"))),
        "legacy_contribution_work": (
            "part1_legacy_contribution_work", r"\1", None,
            arguments(r"samples\s+as\s+nat", "replay", "bytes", "previous", "maximum")),
        "tier1_coding_style_from_code_block_style": (
            "part1_tier1_coding_style_byte", r"\1", None, "value"),
        "tier1_block_coding_from_code_block_style": (
            "part1_tier1_block_coding_byte", r"\1", None, "value"),
    }
    return {
        **{(_coverage_definition_path("src/packet.rs", name), name): value for name, value in packet_contracts.items()},
        **{(_coverage_definition_path("src/tier1.rs", name), name): value for name, value in tier1_contracts.items()},
    }


_PACKET_HEADER_CONTRACTS = _packet_header_contracts()


def _packet_progression_contracts() -> dict[tuple[str, str], tuple[str, str, str | None, str]]:
    def args(*values: str) -> str:
        return r"\s*,\s*".join(values)

    def old(name: str) -> str:
        return _coverage_call("old", re.escape(name))

    def final(name: str) -> str:
        return _coverage_call("final", re.escape(name))

    def view(name: str, *values: str) -> str:
        return _coverage_call(name, *values)

    def cap(name: str) -> str:
        return view("crate::limits::resource_" + name + "_limit", "limits")

    grid = view("packet_grid_view", "grid")
    own_grid = view("packet_grid_view", "self")
    changes = view("crate::codestream::progression_changes_view", "changes")
    params = view("progression_tile_parameters_view", "params")
    progress_old = view("progression_tile_progress_view", old("p"))
    progress_final = view("progression_tile_progress_view", final("p"))
    execution_old = view("progression_tile_execution_view", old("precincts"), old("p"))
    execution_final = view("progression_tile_execution_view", final("precincts"), final("p"))
    precinct_vector = view("packet_precinct_vector_view", "precincts")
    precinct_vector_old = view("packet_precinct_vector_view", old("precincts"))
    precinct_vector_final = view("packet_precinct_vector_view", final("precincts"))
    selection = view("packet_selection_view", "selection")
    initial_payload = (
        r"crate::specs::Part1TilePacketPreparation\s*\{\s*tile_index\s*,\s*index\s*:\s*0\s*,\s*"
        r"payload_bytes\s*:\s*0\s*,\s*packed_payload_bytes\s*:\s*0\s*,\s*declared_packets\s*:\s*0\s*,\s*"
        r"all_lengths\s*:\s*true\s*,\s*packed\s*:\s*" + view("Seq::empty") + r"\s*,?\s*\}"
    )
    packet_contracts = {
        "PacketGrid::total_precinct_count": ("part1_packet_grid_total_precincts", r"\1", None, own_grid),
        "PacketGrid::selected_packet_count": (
            "part1_packet_grid_selected_count", r"\1", None, args(own_grid, "resolution_counts@")),
        "PacketGrid::precinct_count": (
            "part1_packet_grid_precinct_count", r"\1", None, args(own_grid, "component", "resolution")),
        "PacketGrid::precinct_index": (
            "part1_packet_grid_precinct_index", r"\1", None, args(own_grid, "component", "resolution", "precinct")),
        "packet_grid_resolution_summary": (
            "part1_grid_resolution_summary", r"\1", None, args("values@", "0", "0", "false")),
        "packet_grid_count_summary": (
            "part1_grid_count_summary", view("packet_grid_count_outcome", r"\1"), None,
            args("counts@", "component_resolutions@", "resolutions", "expected")),
        "packet_grid_selected_precincts": (
            "part1_grid_selected_precincts", r"\1", None,
            args(selection, "component_resolutions@", "counts@", "resolutions", "components", "initial_total")),
        "packet_grid_new_with_component_resolutions": (
            "part1_packet_grid_new", view("packet_grid_outcome", r"\1"), None,
            args("layers", "components", "component_resolutions@", "precinct_counts@", "None", "limits")),
        "packet_grid_new_with_selected_resolutions": (
            "part1_packet_grid_new", view("packet_grid_outcome", r"\1"), None,
            args("layers", "components", "component_resolutions@", "precinct_counts@",
                 view("packet_selection_view", "selected_resolution_counts"), "limits")),
        "packet_iterator_new": (
            "part1_packet_iterator_initial", view("packet_iterator_view", r"&\s*\1"), None, args(grid, "order")),
        "PacketIterator::decode_candidate": (
            "part1_packet_candidate", r"\1", None, args(view("packet_grid_view", r"self\.grid"), r"self\.order", "candidate")),
        "PacketIterator::next_packet": (
            "part1_packet_iterator_next", r"\1", view("packet_iterator_view", final("self")),
            view("packet_iterator_view", old("self"))),
        "progression_packet_iterator_new": (
            "part1_progression_iterator_initial", view("progression_packet_iterator_outcome", r"\1"), None,
            args(grid, "default_order", changes, cap("work"))),
        "ProgressionPacketIterator::next_packet": (
            "part1_progression_iterator_next", r"\1", view("progression_packet_iterator_view", final("self")),
            view("progression_packet_iterator_view", old("self"))),
        "ProgressionPacketIterator::candidate_step": (
            "part1_progression_candidate_step", r"\1", view("progression_packet_iterator_view", final("self")),
            args(view("progression_packet_iterator_view", old("self")), "record")),
        "ProgressionPacketIterator::next_window": (
            "part1_progression_next_window", r"\1", view("progression_packet_iterator_view", final("self")),
            view("progression_packet_iterator_view", old("self"))),
        "progression_prior_contains": (
            "part1_progression_prior_contains", r"\1", None, args(changes, "end", "0", "coordinate")),
        "window_candidate_count": ("part1_packet_window_count", r"\1", None, args(grid, "record")),
        "decode_window_candidate": (
            "part1_packet_window_candidate", r"\1", None, args(grid, "record", "candidate")),
        "unravel": (
            "part1_packet_unravel", view("packet_unravel_outcome", r"\1"), None, args("index", "dimensions@")),
        "progression_resolution_levels": (
            "part1_progression_resolution_levels", r"\1", None, args("first", "components", "0", "0")),
        "validate_progression_selection": (
            "part1_progression_selection_check", r"\1", None, args("counts@", "available@", "0")),
        "validate_progression_layout": (
            "part1_progression_layout", r"\1", None, args("tile_parts@", grid, selection, "limits")),
        "prepare_progression_payloads": (
            "part1_progression_payloads", view("progression_tile_preparation_outcome", r"\1"), None,
            args("tile_parts@", initial_payload, cap("packet_header_byte"))),
        "validate_progression_precinct_layout": (
            "part1_progression_precinct_layout", r"\1", None, args(grid, precinct_vector)),
        "prepare_progression_tile_input": (
            "part1_progression_tile_input", view("progression_tile_preparation_outcome", r"\1"), None,
            args("tile_parts@", grid, precinct_vector, selection, "limits")),
        "progression_tile_progress_new": (
            "part1_tile_progress_initial", view("progression_tile_progress_outcome", r"\1"), None, params),
        "advance_progression_tile_part": (
            "part1_tile_boundary", r"\1", progress_final, args(params, progress_old)),
        "scan_progression_tile_boundary": (
            "part1_tile_boundary_scan", r"\1", progress_final, args(params, progress_old)),
        "set_progression_context_layer": (
            "part1_packet_context_layers", r"\1", final("contexts") + "@", args(old("contexts") + "@", "layer")),
        "decode_progression_precinct_packet": (
            "part1_tile_precinct_packet", r"\1", view("packet_precinct_view", final("precinct")),
            args(params, r"\*\s*part", view("progression_tile_progress_view", "p"), "coordinate", "expected",
                 view("packet_precinct_view", old("precinct")))),
        "execute_progression_packet": (
            "part1_tile_packet", r"\1", execution_final, args(params, execution_old, "coordinate")),
        "progression_packet_slot": (
            "part1_tile_packet_slot", r"\1", None, args(grid, "coordinate")),
        "omit_progression_packet": (
            "part1_tile_omit_packet", r"\1", progress_final,
            args(params, progress_old, "coordinate", "precinct_count")),
        "all_progression_packets_seen": (
            "part1_tile_all_seen", r"\1", None, "seen@"),
        "account_progression_packet": (
            "part1_tile_account", r"\1", progress_final,
            args(progress_old, "decoded", "tile_bytes", "packed_bytes", "expected", "seen_index")),
        "run_progression_tile_packets": (
            "part1_tile_run", r"\1", execution_final, args(params, execution_old)),
        "finish_progression_tile_packets": (
            "part1_tile_finish", r"\1", progress_final, args(params, progress_old)),
        "decode_progression_tile_packets_selected": (
            "part1_progression_tile_decode", r"\1", precinct_vector_final,
            args("tile_parts@", grid, precinct_vector_old, view("packet_selection_view", "maximum_resolution_counts"), "limits")),
        "decode_progression_tile_packets": (
            "part1_progression_tile_decode", r"\1", precinct_vector_final,
            args("tile_parts@", grid, precinct_vector_old, "None", "limits")),
    }
    input_contracts = {
        "packet_input_limit": ("part1_packet_input_limit", r"\1", None, args("resource", "limit", "actual")),
        "PackedPacketHeaders::reassemble": (
            "part1_packed_header_reassembly", view("packed_header_reassembly_outcome", r"\1"), None,
            args(view("packed_packet_headers_view", "self"), cap("packet_header_byte"))),
        "PacketLengths::iter": (
            "part1_packet_lengths_iter", view("packet_length_iter_view", r"&\s*\1"), None, view("packet_lengths_view", "self")),
        "PacketLengthIter::next_length": (
            "part1_packet_length_next", r"\1", view("packet_length_iter_view", final("self")),
            view("packet_length_iter_view", old("self"))),
        "decode_packet_length": (
            "part1_packet_length_decode", r"\1", None, args("encoded@", "start", "end")),
    }
    return {
        **{(_coverage_definition_path("src/packet.rs", name), name): value for name, value in packet_contracts.items()},
        **{(_coverage_definition_path("src/codestream.rs", name), name): value for name, value in input_contracts.items()},
    }


_PACKET_PROGRESSION_CONTRACTS = _packet_progression_contracts()


def _packet_wrapper_contracts() -> dict[tuple[str, str], tuple[str, str, str | None, str]]:
    def args(*values: str) -> str:
        return r"\s*,\s*".join(values)

    def old(name: str) -> str:
        return _coverage_call("old", re.escape(name))

    def final(name: str) -> str:
        return _coverage_call("final", re.escape(name))

    def view(name: str, *values: str) -> str:
        return _coverage_call(name, *values)

    def cap(name: str, owner: str = "limits") -> str:
        return view("crate::limits::resource_" + name + "_limit", re.escape(owner))

    body_caps = args(*(cap(name) for name in ("code_block_pass", "code_block_byte", "input_byte", "work")))
    parameter_caps = args(*(cap(name, "params.limits") for name in (
        "code_block_pass", "code_block_byte", "input_byte", "work",
    )))
    single_old = view("single_packet_state_view", *(old(name) for name in (
        "state", "inclusion_tree", "zero_bitplane_tree", "decoder",
    )))
    single_final = view("single_packet_state_view", *(final(name) for name in (
        "state", "inclusion_tree", "zero_bitplane_tree", "decoder",
    )))
    multi_old = view("multi_packet_state_view", old("states"), old("inclusion"), old("zero"), "contexts", old("decoders"))
    multi_final = view("multi_packet_state_view", final("states"), final("inclusion"), final("zero"), "contexts", final("decoders"))
    bundle_old = view("multi_packet_state_view", old("execution.states"), old("execution.inclusion_tree"),
                      old("execution.zero_bitplane_tree"), r"execution\.contexts", old("execution.decoders"))
    bundle_final = view("multi_packet_state_view", final("execution.states"), final("execution.inclusion_tree"),
                        final("execution.zero_bitplane_tree"), r"execution\.contexts", final("execution.decoders"))
    header_old = view("multi_header_view", old("states"), old("inclusion"), old("zero"),
                      r"parameters\.contexts", old("contributions"), old("reader"), old("progress"))
    header_final = view("multi_header_view", final("states"), final("inclusion"), final("zero"),
                        r"parameters\.contexts", final("contributions"), final("reader"), final("progress"))
    decoder_map = (
        r"@\s*\.map_values\s*\(\s*\|\s*decoder\s*:\s*Tier1CodeBlockDecoder\s*\|\s*"
        + view("crate::tier1::tier1_decoder_state", r"&\s*decoder") + r"\s*\)"
    )
    values = {
        "decode_single_code_block_packet": (
            "part1_single_code_block_packet", r"\1", single_final,
            args(single_old, "payload@", "context", cap("packet_header_byte"), body_caps)),
        "decode_multi_code_block_packet": (
            "part1_multi_code_block_packet", r"\1", bundle_final, args(bundle_old, "tile_part", "offset", "limits")),
        "decode_jpip_precinct_packet_inner": (
            "part1_jpip_precinct_packet_inner", r"\1", view("packet_precinct_view", final("precinct")),
            args(view("packet_precinct_view", old("precinct")), "template", "data@", "expected_sop_sequence", "layer", "limits")),
        "decode_jpip_precinct_packet": (
            "part1_jpip_precinct_packet", r"\1", view("packet_precinct_view", final("precinct")),
            args(view("packet_precinct_view", old("precinct")), "template", "data@", "expected_sop_sequence", "layer", "limits")),
        "preflight_packet_body_ranges": (
            "part1_packet_body_preflight_at", r"\1", view("packet_body_preflight_view", final("progress")),
            args(view("packet_body_preflight_view", old("progress")), view("packet_body_contributions_view", "contributions"),
                 "data@", r"error_offsets\.0", r"error_offsets\.1")),
        "execute_packet_body_contributions": (
            "part1_packet_body_execute_at", r"\1", view("packet_body_execution_view", final("decoders"), final("progress")),
            args(view("packet_body_execution_view", old("decoders"), old("progress")),
                 view("packet_body_contributions_view", "contributions"), "data@", r"error_offsets\.0",
                 r"error_offsets\.1", "decode_tier1", body_caps)),
        "validate_multi_packet_contexts": (
            "part1_multi_contexts", r"\1", None, args("contexts@", "style", "layer", "width", "0", "offset")),
        "validate_multi_packet_input": (
            "part1_multi_packet_admission", view("multi_admission_outcome", r"\1"), None,
            args(view("multi_packet_state_view", "states", "inclusion", "zero", "contexts", "decoders"),
                 r"params\.part", r"params\.offset", cap("code_block", "params.limits"), cap("work", "params.limits"))),
        "read_multi_packet_prefix": (
            "part1_multi_packet_prefix", view("precinct_payload_reader_outcome", r"\1"), None,
            args("data@", "sop", "offset", cap("packet_header_byte"), cap("work"))),
        "read_multi_packet_header_slot": (
            "part1_multi_header_slot", r"\1", header_final, args(header_old, r"parameters\.offset")),
        "read_multi_packet_headers": (
            "part1_multi_headers", r"\1", header_final, args(header_old, r"parameters\.offset")),
        "multi_packet_body_start": (
            "part1_multi_body_start", r"\1", None, args("data@", "sop", "header", "eph", "offset")),
        "decode_multi_packet_body": (
            "part1_multi_body_data", r"\1", final("decoders") + decoder_map,
            args(old("decoders") + decoder_map, r"layout\.blocks", "data@",
                 view("packet_body_contributions_view", "contributions"), r"layout\.present", r"layout\.count",
                 r"layout\.header", r"layout\.start", r"params\.offset", parameter_caps)),
        "decode_multi_packet_payload": (
            "part1_multi_payload", r"\1", multi_final,
            args(multi_old, "data@", view("crate::codestream::coding_style_packet_markers", r"&\s*params\.part\.coding_style") + r"\.0",
                 view("crate::codestream::coding_style_packet_markers", r"&\s*params\.part\.coding_style") + r"\.1",
                 r"params\.offset", cap("packet_header_byte", "params.limits"), parameter_caps)),
    }
    return {(_coverage_definition_path("src/packet.rs", name), name): value for name, value in values.items()}


_PACKET_WRAPPER_CONTRACTS = _packet_wrapper_contracts()
_PACKET_EXECUTION_BUNDLE_FIELDS = frozenset({"states", "inclusion_tree", "zero_bitplane_tree", "decoders"})
_PACKET_PROVED_BOUNDARY_APIS = frozenset({
    ("src/packet/multi_packet.rs", "decode_single_code_block_packet"),
    ("src/packet/multi_packet.rs", "decode_multi_code_block_packet"),
})

def _reconstruction_contracts() -> dict[tuple[str, str], tuple[str, str, str | None, str]]:
    def args(*values: str) -> str:
        return r"\s*,\s*".join(values)

    def old(name: str) -> str:
        return _coverage_call("old", re.escape(name))

    def final(name: str) -> str:
        return _coverage_call("final", re.escape(name))

    def view(name: str, *values: str) -> str:
        return _coverage_call(name, *values)

    def cap(name: str) -> str:
        return view("crate::limits::resource_" + name + "_limit", "limits")

    caps = args(cap("work"), cap("decoded_bytes"))
    components_old = view("transform_components_view", old("components"))
    components_final = args(view("transform_components_view", final("components")), r"\*\s*" + final("work"))
    work_old = r"\*\s*" + old("work")
    collection = view("crate::codestream::mct_collection_view", "collection")
    stage = view("crate::codestream::mct_stage_view", "stage") + r"\s*\.1"
    stages = view("crate::codestream::multiple_component_transform_view", "transform")
    prepared_old = view("prepared_components_view", old("prepared") + r"\s*@")
    prepared_final = view("prepared_components_view", final("prepared") + r"\s*@")
    size = args(view("codestream::image_size_component_count", "size"), view("codestream::image_size_component_infos", "size"))
    owner_array = r"\s*@\s*\.len\s*\(\s*\)"
    prepared_map_old = view("Seq::new", old("prepared") + owner_array,
        r"\|\s*index\s*:\s*int\s*\|\s*" + view("prepared_component_view", old("prepared") + r"\s*@\s*\[\s*index\s*\]"))
    prepared_map_final = view("Seq::new", final("prepared") + owner_array,
        r"\|\s*index\s*:\s*int\s*\|\s*" + view("prepared_component_view", final("prepared") + r"\s*@\s*\[\s*index\s*\]"))
    image_contracts = {
        "inverse_reversible_mct": ("part2_inverse_reversible_mct",
            view("crate::transform::sequence_outcome", r"\1"), None,
            args(view("crate::codestream::mct_array_view", "matrix"), "source@")),
        "prepare_mct_decorrelation": ("part2_mct_prepare_decorrelation",
            view("mct_decorrelation_preparation_outcome", r"\1"), r"\*\s*" + final("work"),
            args(view("transform_components_view", "components"), collection, work_old, caps)),
        **{name: (model, r"\1", components_final, args(components_old, collection, work_old, caps))
           for name, model in (
               ("apply_mct_dependency", "part2_mct_dependency"),
               ("apply_mct_decorrelation", "part2_mct_decorrelation"),
               ("apply_mct_wavelet", "part2_mct_wavelet"),
               ("apply_mct_collection", "part2_mct_collection"),
           )},
        "apply_mct_stage": ("part2_mct_stage_prefix", r"\1", components_final,
            args(components_old, stage, work_old, caps, stage + r"\s*\.len\s*\(\s*\)")),
        "apply_multiple_component_transform_components": ("part2_mct_transform", r"\1", components_final,
            args(components_old, stages, work_old, caps)),
        "apply_multiple_component_transform": ("part2_mct_decoded_image", r"\1",
            view("decoded_image_view", r"\*\s*" + final("image")),
            args(view("decoded_image_view", r"\*\s*" + old("image")), stages, caps)),
    }
    decode_contracts = {
        ("src/decode/reconstruction.rs", "apply_tile_multiple_component_transform"): ("part2_mct_prepared_tiles", r"\1",
            args(prepared_map_final, r"\*\s*" + final("work")), args(prepared_map_old, size,
                view("codestream::multiple_component_transform_view", "transform"), work_old, caps)),
        ("src/decode/execution.rs", "finish_prepared_tile"): ("part2_finish_prepared_tile", r"\1",
            args(prepared_final, r"\*\s*" + final("work")),
            args(prepared_old, size, view("tile_mct_option", "mct"), "standard", work_old, caps)),
        ("src/decode/execution.rs", "reconstruct_planned_tile"): ("part2_reconstruct_planned_tile", r"\1",
            args(prepared_final, r"\*\s*" + final("work")),
            args(prepared_old, view("planned_components_view", "plan"), view("prepare_precincts_view", r"plan\.precincts@"),
                 r"first\.component_coding_styles", view("codestream::part2_kernel_registry", r"&\s*first\.part2_extensions"),
                 size, view("tile_part_mct_view", "first"), "standard", work_old, caps)),
        ("src/decode/execution.rs", "apply_prepared_component_transform"): ("part1_prepared_standard_transform", r"\1", prepared_final,
            args(prepared_old, "transform")),
        ("src/decode/reconstruction.rs", "assemble_prepared_components"): ("part2_assemble_prepared", view("crate::image::decoded_image_outcome", r"\1"), None,
            args(view("crate::image::assembly_size_view", "size"), view("prepared_components_view", "prepared@"), "selection", cap("decoded_bytes"))),
        ("src/decode/code_blocks.rs", "decode_prepared_image"): ("part1_decode_prepared_image", view("crate::image::decoded_image_outcome", r"\1"), None,
            args(view("crate::image::assembly_size_view", "size"), view("crate::image::assembly_tiles_view", "tile_components@"),
                 "component_transform", cap("decoded_bytes"))),
        ("src/decode/reconstruction.rs", "decode_progression_prepared_image"): ("part1_progression_prepared_image", view("crate::image::decoded_image_outcome", r"\1"), None,
            args(view("crate::image::assembly_size_view", "size"),
                 *(view("progression_reconstruction_view", "plan") + rf"\s*\.{index}" for index in range(4)),
                 cap("decoded_bytes"))),
    }
    return {
        **{(_coverage_definition_path("src/image.rs", name), name): recipe for name, recipe in image_contracts.items()},
        **decode_contracts,
        ("src/codestream/extensions.rs", "Part2Extensions::arbitrary_kernel"): (
            "part2_kernel_registry_lookup", view("crate::transform::arbitrary_kernel_option", r"\1"), None,
            args(view("part2_kernel_registry", "self"), "index")),
    }


_RECONSTRUCTION_CONTRACTS = _reconstruction_contracts()
_RECONSTRUCTION_PROVED_BOUNDARY_APIS = frozenset({
    ("src/image/mct.rs", "apply_multiple_component_transform"),
    ("src/decode/reconstruction.rs", "decode_progression_prepared_image"),
})

_LAYER_STATE_CONTRACTS = {
    ("src/jpx/chroma.rs", "apply_chroma_key"): (
        "part2_apply_chroma_key", r"\1",
        _coverage_call("owned_layer_view", _coverage_call("final", "owned")),
        _coverage_call("owned_layer_view", _coverage_call("old", "owned")) + r"\s*,\s*keys\s*@",
    ),
}

_TRANSFORM_ARRAY_BYTES_CONTRACTS = {
    ("src/codestream/reader.rs", "read_u64"): (
        "part1_codestream_u64", r"\1", None, r"bytes\s*@",
    ),
    ("src/codestream/reader.rs", "signed_u16"): (
        "part1_signed_u16", r"\1", None, "value",
    ),
    ("src/codestream/mct_markers.rs", "fixed_from_binary"): (
        "part1_fixed_from_binary", r"\1", None, r"negative\s*,\s*significand\s*,\s*binary_exponent",
    ),
    ("src/codestream/mct_markers.rs", "float32_to_fixed"): (
        "part1_float32_to_fixed", r"\1", None, "bits",
    ),
    ("src/codestream/mct_markers.rs", "float64_to_fixed"): (
        "part1_float64_to_fixed", r"\1", None, "bits",
    ),
    ("src/codestream/mct_markers.rs", "Parser::decode_mct_element"): (
        "part1_mct_element", r"\1", None, r"offset\s*,\s*data\s*@\s*,\s*position\s*,\s*numeric_format",
    ),
    ("src/codestream/mct_markers.rs", "Parser::parse_mct"): (
        "part1_parse_mct", _coverage_call("mct_array_outcome", r"\1"), None,
        _coverage_call("segment_view", "segment") + r"\s*,\s*self\.limits",
    ),
}

_COLLECTION_FRAGMENT_CONTRACTS = {
    ("src/codestream/mct_markers.rs", "find_mcc_fragment"): (
        "part1_mcc_fragment_find", r"\1", None,
        _coverage_call("mcc_pending_view", r"pending\s*@") + r"\s*,\s*index\s*,\s*0",
    ),
    ("src/codestream/mct_resolution.rs", "u8_list_contains"): (
        "part1_byte_list_contains", r"\1", None, r"values\s*@\s*,\s*value",
    ),
    ("src/codestream/mct_markers.rs", "Parser::prepare_mcc_fragment"): (
        "part1_prepare_mcc_fragment", r"\1",
        _coverage_call("mcc_pending_view", _coverage_call("final", "pending") + r"\s*@"),
        _coverage_call("segment_view", "segment") + r"\s*,\s*components\s*,\s*"
        + _coverage_call("mcc_pending_view", _coverage_call("old", "pending") + r"\s*@")
        + r"\s*,\s*completed\s*@",
    ),
    ("src/codestream/mct_markers.rs", "Parser::consume_mcc_fragment"): (
        "part1_consume_mcc_fragment", _coverage_call("mcc_fragment_outcome", r"\1"),
        _coverage_call("mcc_pending_view", _coverage_call("final", "pending") + r"\s*@")
        + r"\s*,\s*" + _coverage_call("final", "completed") + r"\s*@",
        _coverage_call("segment_view", "segment") + r"\s*,\s*components\s*,\s*self\.limits\s*,\s*"
        + _coverage_call("mcc_pending_view", _coverage_call("old", "pending") + r"\s*@")
        + r"\s*,\s*" + _coverage_call("old", "completed") + r"\s*@",
    ),
}

_PACKED_HEADER_BYTES_CONTRACTS = {
    ("src/codestream/packet_headers.rs", "Parser::parse_packed_fragment"): (
        "part1_parse_packed_fragment", r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self"))
        + r"\s*,\s*\*\s*" + _coverage_call("final", "next_index")
        + r"\s*,\s*\*\s*" + _coverage_call("final", "fragments")
        + r"\s*,\s*" + _coverage_call("final", "bytes") + r"\s*@",
        _coverage_call("parser_view", _coverage_call("old", "self"))
        + r"\s*,\s*" + _coverage_call("segment_view", "segment") + r"\s*,\s*expected_marker"
        + r"\s*,\s*\*\s*" + _coverage_call("old", "next_index")
        + r"\s*,\s*\*\s*" + _coverage_call("old", "fragments")
        + r"\s*,\s*" + _coverage_call("old", "bytes") + r"\s*@",
    ),
    ("src/codestream/packet_headers.rs", "Parser::parse_ppm_frames"): (
        "part1_parse_ppm_frames", _coverage_call("packed_header_frames_outcome", r"\1"), None,
        r"bytes\s*@\s*,\s*fragments\s*,\s*self\.limits",
    ),
}

_PACKET_LENGTH_ADMISSION_CONTRACTS = {
    ("src/codestream/packet_headers.rs", "PacketLengths::incomplete_plm_offset"): (
        "part1_incomplete_plm_offset", r"\1", None,
        _coverage_call("packet_lengths_view", "self"),
    ),
    ("src/codestream/packet_headers.rs", "Parser::validate_packet_lengths"): (
        "part1_validate_packet_lengths", r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self")),
        _coverage_call("parser_view", _coverage_call("old", "self"))
        + r"\s*,\s*encoded\s*@\s*,\s*marker_offset",
    ),
    ("src/codestream/packet_headers.rs", "Parser::parse_plm"): (
        "part1_parse_plm", r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self"))
        + r"\s*,\s*\*\s*" + _coverage_call("final", "next_index")
        + r"\s*,\s*" + _coverage_call(
            "packet_length_groups_view", _coverage_call("final", "groups") + r"\s*@"),
        _coverage_call("parser_view", _coverage_call("old", "self"))
        + r"\s*,\s*" + _coverage_call("segment_view", "segment")
        + r"\s*,\s*\*\s*" + _coverage_call("old", "next_index")
        + r"\s*,\s*" + _coverage_call(
            "packet_length_groups_view", _coverage_call("old", "groups") + r"\s*@"),
    ),
}

_TILE_PACKET_ADMISSION_CONTRACTS = {
    ("src/codestream/packet_headers.rs", "Parser::parse_plt"): (
        "part1_parse_plt", r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self"))
        + r"\s*,\s*\*\s*" + _coverage_call("final", "next_index")
        + r"\s*,\s*\*\s*" + _coverage_call("final", "seen")
        + r"\s*,\s*\*\s*" + _coverage_call("final", "packet_count")
        + r"\s*,\s*\*\s*" + _coverage_call("final", "encoded_bytes")
        + r"\s*,\s*\*\s*" + _coverage_call("final", "payload_bytes"),
        _coverage_call("parser_view", _coverage_call("old", "self"))
        + r"\s*,\s*" + _coverage_call("segment_view", "segment")
        + r"\s*,\s*" + _coverage_call("packet_lengths_view", r"&\s*main")
        + r"\s*,\s*\*\s*" + _coverage_call("old", "next_index")
        + r"\s*,\s*\*\s*" + _coverage_call("old", "seen")
        + r"\s*,\s*\*\s*" + _coverage_call("old", "packet_count")
        + r"\s*,\s*\*\s*" + _coverage_call("old", "encoded_bytes")
        + r"\s*,\s*\*\s*" + _coverage_call("old", "payload_bytes"),
    ),
    ("src/codestream/packet_headers.rs", "Parser::parse_ppt"): (
        "part1_parse_ppt", r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self"))
        + r"\s*,\s*\*\s*" + _coverage_call("final", "next_index")
        + r"\s*,\s*\*\s*" + _coverage_call("final", "fragments")
        + r"\s*,\s*" + _coverage_call("final", "bytes") + r"\s*@",
        _coverage_call("parser_view", _coverage_call("old", "self"))
        + r"\s*,\s*" + _coverage_call("segment_view", "segment")
        + r"\s*,\s*" + _coverage_call("packed_packet_headers_view", r"&\s*main")
        + r"\s*,\s*\*\s*" + _coverage_call("old", "next_index")
        + r"\s*,\s*\*\s*" + _coverage_call("old", "fragments")
        + r"\s*,\s*" + _coverage_call("old", "bytes") + r"\s*@",
    ),
}

_PACKET_METADATA_FINALIZATION_CONTRACTS = {
    ("src/codestream/packet_headers.rs", "packet_length_sources_match"): (
        "part1_packet_length_sources_match", r"\1", None,
        _coverage_call("packet_length_source_view", "first") + r"\s*,\s*"
        + _coverage_call("packet_length_source_view", "second"),
    ),
    ("src/codestream/packet_headers.rs", "sum_packet_lengths"): (
        "part1_sum_packet_lengths", r"\1", None,
        _coverage_call("packet_length_source_view", "source"),
    ),
    ("src/codestream/packet_headers.rs", "Parser::finish_packet_lengths"): (
        "part1_finish_packet_lengths", _coverage_call("packet_lengths_outcome", r"\1"), None,
        r"self\.input\s*@\s*,\s*tile_header_start\s*,\s*tile_header_end\s*,\s*"
        + _coverage_call("packet_lengths_view", r"&\s*main_packet_lengths")
        + r"\s*,\s*plt_seen\s*,\s*plt_packet_count\s*,\s*plt_encoded_bytes\s*,\s*plt_payload_bytes"
        + r"\s*,\s*data_length\s*,\s*packed_header_length\s*,\s*tile_part_offset",
    ),
    ("src/codestream/packet_headers.rs", "Parser::finish_packed_packet_headers"): (
        "part1_finish_packed_packet_headers", _coverage_call("packed_packet_headers_outcome", r"\1"), None,
        r"self\.input\s*@\s*,\s*tile_header_start\s*,\s*tile_header_end\s*,\s*"
        + _coverage_call("packed_packet_headers_view", r"&\s*main")
        + r"\s*,\s*ppt_fragments\s*,\s*ppt_length\s*,\s*tile_part_offset",
    ),
}

_TRANSFORM_GRAPH_CONTRACTS = {
    ("src/codestream/mct_resolution.rs", "Parser::expected_mct_elements"): (
        "part1_mct_graph_element_count", r"\1", None,
        r"rows\s*,\s*columns\s*,\s*kind\s*,\s*reversible",
    ),
    ("src/codestream/mct_resolution.rs", "Parser::resolve_mct_collection"): (
        "part1_mct_graph_collection", _coverage_call("mct_collection_outcome", r"\1"), None,
        _coverage_call("mcc_collection_reference_view", "reference") + r"\s*,\s*"
        + _coverage_call("mct_arrays_view", r"arrays\s*@"),
    ),
    ("src/codestream/mct_resolution.rs", "Parser::resolve_mct_stage"): (
        "part1_mct_graph_stage", _coverage_call("mct_stage_outcome", r"\1"), None,
        _coverage_call("mct_record_view", "record") + r"\s*,\s*"
        + _coverage_call("mct_arrays_view", r"arrays\s*@"),
    ),
    ("src/codestream/mct_resolution.rs", "Parser::resolve_multiple_component_transform"): (
        "part1_mct_graph", _coverage_call("mct_graph_outcome", r"\1"), None,
        _coverage_call("mct_parameters_view", "parameters"),
    ),
}

_TRANSFORM_REGISTRY_CONTRACTS = {
    ("src/codestream/mct_resolution.rs", "find_mct_array_index"): (
        "part1_mct_registry_array_find", r"\1", None,
        _coverage_call("mct_arrays_view", r"arrays\s*@") + r"\s*,\s*index\s*,\s*0",
    ),
    ("src/codestream/mct_resolution.rs", "find_mct_record_index"): (
        "part1_mct_registry_record_find", r"\1", None,
        _coverage_call("mct_records_view", r"records\s*@") + r"\s*,\s*index\s*,\s*0",
    ),
    ("src/codestream/mct_resolution.rs", "validate_unique_mct_array_indexes"): (
        "part1_mct_registry_unique_array", r"\1", None,
        _coverage_call("mct_arrays_view", r"arrays\s*@") + r"\s*,\s*marker_offset",
    ),
    ("src/codestream/mct_resolution.rs", "validate_unique_mct_record_indexes"): (
        "part1_mct_registry_unique_record", r"\1", None,
        _coverage_call("mct_records_view", r"records\s*@") + r"\s*,\s*marker_offset",
    ),
    ("src/codestream/mct_resolution.rs", "replace_mct_array"): (
        "part1_mct_registry_replace_array", r"\(\s*\)",
        _coverage_call("mct_arrays_view", _coverage_call("final", "arrays") + r"\s*@"),
        _coverage_call("mct_arrays_view", _coverage_call("old", "arrays") + r"\s*@")
        + r"\s*,\s*" + _coverage_call("mct_array_view", r"&\s*replacement"),
    ),
    ("src/codestream/mct_resolution.rs", "replace_mct_record"): (
        "part1_mct_registry_replace_record", r"\(\s*\)",
        _coverage_call("mct_records_view", _coverage_call("final", "records") + r"\s*@"),
        _coverage_call("mct_records_view", _coverage_call("old", "records") + r"\s*@")
        + r"\s*,\s*" + _coverage_call("mct_record_view", r"&\s*replacement"),
    ),
    ("src/codestream/mct_resolution.rs", "referenced_mct_array"): (
        "part1_mct_registry_reference", _coverage_call("mct_array_reference_outcome", r"\1"), None,
        _coverage_call("mct_arrays_view", r"arrays\s*@") + r"\s*,\s*index\s*,\s*kind",
    ),
}

_TRANSFORM_FRAGMENT_CONTRACTS = {
    ("src/codestream/mct_markers.rs", "find_mct_fragment"): (
        "part1_mct_fragment_find", r"\1", None,
        _coverage_call("mct_pending_view", r"pending\s*@") + r"\s*,\s*index\s*,\s*0",
    ),
    ("src/codestream/mct_resolution.rs", "u8_list_contains"): _COLLECTION_FRAGMENT_CONTRACTS[
        ("src/codestream/mct_resolution.rs", "u8_list_contains")
    ],
    ("src/codestream/mct_markers.rs", "Parser::prepare_mct_fragment"): (
        "part1_prepare_mct_fragment", r"\1",
        _coverage_call("mct_pending_view", _coverage_call("final", "pending") + r"\s*@"),
        _coverage_call("segment_view", "segment") + r"\s*,\s*self\.limits\s*,\s*"
        + _coverage_call("mct_pending_view", _coverage_call("old", "pending") + r"\s*@")
        + r"\s*,\s*completed\s*@",
    ),
    ("src/codestream/mct_markers.rs", "Parser::consume_mct_fragment"): (
        "part1_consume_mct_fragment", _coverage_call("mct_fragment_outcome", r"\1"),
        _coverage_call("mct_pending_view", _coverage_call("final", "pending") + r"\s*@")
        + r"\s*,\s*" + _coverage_call("final", "completed") + r"\s*@",
        _coverage_call("segment_view", "segment") + r"\s*,\s*self\.limits\s*,\s*"
        + _coverage_call("mct_pending_view", _coverage_call("old", "pending") + r"\s*@")
        + r"\s*,\s*" + _coverage_call("old", "completed") + r"\s*@",
    ),
}

_TRANSFORM_COLLECTION_BYTES_CONTRACTS = {
    ("src/codestream/reader.rs", "signed_u32"): (
        "part1_signed_u32", r"\1", None, "value",
    ),
    ("src/codestream/mct_resolution.rs", "component_lists_overlap"): (
        "part1_mcc_lists_overlap", r"\1", None, r"left\s*@\s*,\s*right\s*@",
    ),
    ("src/codestream/mct_resolution.rs", "validate_parallel_collections"): (
        "part1_mcc_parallel_collections", r"\1", None,
        _coverage_call("mcc_collection_references_view", r"collections\s*@") + r"\s*,\s*marker_offset",
    ),
    ("src/codestream/mct_markers.rs", "Parser::decode_mcc_collection"): (
        "part1_mcc_collection", _coverage_call("mcc_collection_outcome", r"\1"), None,
        _coverage_call("segment_view", "segment") + r"\s*,\s*components\s*,\s*start",
    ),
    ("src/codestream/mct_markers.rs", "Parser::parse_mcc"): (
        "part1_parse_mcc", _coverage_call("mcc_record_outcome", r"\1"), None,
        _coverage_call("segment_view", "segment") + r"\s*,\s*components\s*,\s*self\.limits",
    ),
}

_TRANSFORM_ROUTING_BYTES_CONTRACTS = {
    ("src/codestream/mct_markers.rs", "Parser::parse_mco"): (
        "part1_parse_mco", _coverage_call("segment_tail_outcome", r"\1"), None,
        _coverage_call("segment_view", "segment"),
    ),
    ("src/codestream/mct_markers.rs", "parse_mcc_component_list"): (
        "part1_parse_mcc_component_list", _coverage_call("marker_words_outcome", r"\1"),
        r"\*\s*" + _coverage_call("final", "position"),
        r"payload\s*@\s*,\s*\*\s*" + _coverage_call("old", "position")
        + r"\s*,\s*components\s*,\s*marker_offset",
    ),
    ("src/codestream/mct_markers.rs", "u16_list_contains"): (
        "part1_mcc_reference_present", r"\1", None, r"values\s*@\s*,\s*value",
    ),
}

_PROGRESSION_ADMISSION_CONTRACTS = {
    ("src/codestream/coding_markers.rs", "Parser::progression_validation_shape"): (
        "part1_poc_validation_shape", r"\1", None,
        r"offset\s*,\s*layers\s*,\s*component_styles\s*,\s*0\s*,\s*0\s*,\s*0",
    ),
    ("src/codestream/coding_markers.rs", "Parser::mark_progression_resolutions"): (
        "part1_poc_mark_resolutions", r"\1", _coverage_call("final", "owners") + r"\s*@",
        r"offset\s*,\s*record\s*,\s*coordinate\s*,\s*0\s*,\s*"
        + _coverage_call("old", "owners") + r"\s*@\s*,\s*progress",
    ),
    ("src/codestream/coding_markers.rs", "Parser::mark_progression_layers"): (
        "part1_poc_mark_layers", r"\1", _coverage_call("final", "owners") + r"\s*@",
        r"offset\s*,\s*record\s*,\s*coordinate\s*,\s*layers\s*,\s*0\s*,\s*"
        + _coverage_call("old", "owners") + r"\s*@\s*,\s*progress",
    ),
    ("src/codestream/coding_markers.rs", "Parser::mark_progression_record"): (
        "part1_poc_mark_record", r"\1", _coverage_call("final", "owners") + r"\s*@",
        r"offset\s*,\s*record\s*,\s*layers\s*,\s*component_styles\s*,\s*"
        + _coverage_call("old", "owners") + r"\s*@",
    ),
    ("src/codestream/coding_markers.rs", "progression_owners_complete"): (
        "part1_progression_owners_complete", r"\1", None, r"owners\s*@",
    ),
    ("src/codestream/coding_markers.rs", "Parser::validate_progression_changes"): (
        "part1_validate_progression_changes", r"\1", None,
        r"offset\s*,\s*" + _coverage_call("progression_changes_view", "changes")
        + r"\s*,\s*layers\s*,\s*component_styles\s*,\s*self\.limits",
    ),
}

_PROGRESSION_BYTES_CONTRACTS = {
    ("src/codestream/coding_markers.rs", "Parser::read_poc_byte"): (
        "part1_poc_byte", r"\1", None,
        _coverage_call("segment_view", "segment") + r"\s*,\s*position",
    ),
    ("src/codestream/coding_markers.rs", "Parser::read_poc_component"): (
        "part1_poc_component", r"\1", None,
        _coverage_call("segment_view", "segment") + r"\s*,\s*position\s*,\s*width",
    ),
    ("src/codestream/coding_markers.rs", "Parser::parse_poc"): (
        "part1_parse_poc", _coverage_call("parsed_progression_outcome", r"\1"), None,
        _coverage_call("segment_view", "segment") + r"\s*,\s*components",
    ),
}

_KERNEL_BYTES_CONTRACTS = {
    ("src/codestream/part2_transforms.rs", "Parser::read_kernel_coefficient"): (
        "part1_kernel_coefficient", _coverage_call("kernel_coefficient_outcome", r"\1"), None,
        r"self\.position\s*,\s*" + _coverage_call("segment_view", "segment")
        + r"\s*,\s*position\s*,\s*width\s*,\s*coefficient_type",
    ),
    ("src/codestream/part2_transforms.rs", "Parser::decode_atk_step"): (
        "part1_atk_step", _coverage_call("kernel_step_outcome", r"\1"), None,
        r"self\.position\s*,\s*" + _coverage_call("segment_view", "segment")
        + r"\s*,\s*start\s*,\s*width\s*,\s*coefficient_type\s*,\s*reversible\s*,\s*whole_sample_filter",
    ),
    ("src/codestream/part2_transforms.rs", "Parser::decode_atk_payload"): (
        "part1_atk_payload", _coverage_call("atk_payload_outcome", r"\1"), None,
        r"self\.position\s*,\s*" + _coverage_call("segment_view", "segment"),
    ),
    ("src/codestream/part2_transforms.rs", "Parser::parse_atk"): (
        "part1_parse_atk", r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self")) + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("final", "extensions")),
        _coverage_call("parser_view", _coverage_call("old", "self")) + r"\s*,\s*"
        + _coverage_call("segment_view", "segment") + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("old", "extensions")),
    ),
}

_TILE_LENGTH_BYTES_CONTRACTS = {
    ("src/codestream/image_header.rs", "Parser::parse_tlm"): (
        "part1_parse_tlm", r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self")) + r"\s*,\s*\*\s*"
        + _coverage_call("final", "next_index") + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("final", "extensions")),
        _coverage_call("parser_view", _coverage_call("old", "self")) + r"\s*,\s*"
        + _coverage_call("segment_view", "segment") + r"\s*,\s*\*\s*"
        + _coverage_call("old", "next_index") + r"\s*,\s*tile_count\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("old", "extensions")),
    ),
}

_NONLINEAR_BYTES_CONTRACTS = {
    ("src/codestream/profile.rs", "maximum_u32_for_bits"): (
        "part1_maximum_u32_for_bits", r"\1", None, "bits",
    ),
    ("src/codestream/reader.rs", "Parser::copy_segment_tail"): (
        "part1_copy_segment_tail", _coverage_call("segment_tail_outcome", r"\1"), None,
        _coverage_call("segment_view", "segment") + r"\s*,\s*start",
    ),
    ("src/codestream/part2_transforms.rs", "Parser::decode_nlt_gamma"): (
        "part1_nlt_gamma", r"\1", None, _coverage_call("segment_view", "segment"),
    ),
    ("src/codestream/part2_transforms.rs", "Parser::decode_nlt_payload"): (
        "part1_nlt_payload", _coverage_call("nlt_payload_outcome", r"\1"), None,
        _coverage_call("segment_view", "segment") + r"\s*,\s*components",
    ),
    ("src/codestream/part2_transforms.rs", "Parser::parse_nlt"): (
        "part1_parse_nlt", r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self")) + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("final", "extensions")),
        _coverage_call("parser_view", _coverage_call("old", "self")) + r"\s*,\s*"
        + _coverage_call("segment_view", "segment") + r"\s*,\s*components\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("old", "extensions")),
    ),
}

_PROFILE_BYTES_CONTRACTS = {
    ("src/codestream/profile.rs", "count_set_bits"): (
        "part1_set_bits_prefix", r"\1\s+as\s+nat", None, r"value\s*,\s*32",
    ),
    ("src/codestream/profile.rs", "Parser::read_marker_words"): (
        "part1_marker_words", _coverage_call("marker_words_outcome", r"\1"), None,
        _coverage_call("segment_view", "segment") + r"\s*,\s*start",
    ),
    ("src/codestream/profile.rs", "Parser::parse_cap"): (
        "part1_parse_cap", _coverage_call("cap_payload_outcome", r"\1"), None,
        _coverage_call("segment_view", "segment"),
    ),
    ("src/codestream/profile.rs", "Parser::parse_profile_number"): (
        "part1_parse_profile_number", _coverage_call("profile_number_outcome", r"\1"), None,
        _coverage_call("segment_view", "segment"),
    ),
}

_COMPONENT_HEADER_APPLICATION_CONTRACTS = {
    ("src/codestream/image_header.rs", "component_depths_uniform"): (
        "part1_component_depths_uniform", r"\1", None,
        _coverage_call("parsed_image_size_view", "size") + r"\s*,\s*first",
    ),
    ("src/codestream/image_header.rs", "Parser::apply_component_bit_depths"): (
        "part1_apply_component_depths", r"\1",
        _coverage_call("parsed_image_size_view", _coverage_call("final", "size")),
        _coverage_call("parsed_image_size_view", _coverage_call("old", "size"))
        + r"\s*,\s*depths\s*@\s*,\s*self\.position",
    ),
    ("src/codestream/image_header.rs", "Parser::apply_component_registrations"): (
        "part1_apply_component_registrations", r"\1",
        _coverage_call("parsed_image_size_view", _coverage_call("final", "size")),
        _coverage_call("parsed_image_size_view", _coverage_call("old", "size"))
        + r"\s*,\s*registrations\s*@\s*,\s*self\.position",
    ),
}

_COMPONENT_DEPTH_BYTES_CONTRACTS = {
    ("src/codestream/image_header.rs", "Parser::parse_cbd"): (
        "part1_parse_cbd", r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self")) + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("final", "extensions")),
        _coverage_call("parser_view", _coverage_call("old", "self")) + r"\s*,\s*"
        + _coverage_call("segment_view", "segment") + r"\s*,\s*components\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("old", "extensions")),
    ),
}

_MAIN_COMPONENT_FINALIZATION_CONTRACTS = {
    ("src/codestream/coding_style.rs", "new_component_coding_styles"): (
        "part1_component_styles_new", _coverage_call("parsed_style_owner_outcome", r"\1"), None,
        r"components\s*,\s*" + _coverage_call("parsed_coding_style_view", "default"),
    ),
    ("src/codestream/quantization.rs", "new_component_quantizations"): (
        "part1_component_quantizations_new", _coverage_call("parsed_quantization_owner_outcome", r"\1"), None,
        r"components\s*,\s*" + _coverage_call("quantization_view", r"&\s*default"),
    ),
    ("src/codestream/quantization.rs", "ComponentQuantizations::set"): (
        "part1_set_component_quantization", r"\1",
        _coverage_call("parsed_quantization_owner_view", _coverage_call("final", "self")),
        _coverage_call("parsed_quantization_owner_view", _coverage_call("old", "self"))
        + r"\s*,\s*component\s*,\s*" + _coverage_call("quantization_view", r"&\s*quantization"),
    ),
    ("src/codestream/quantization.rs", "Quantization::is_compatible_with"): (
        "part1_quantization_compatible", r"\1", None,
        _coverage_call("quantization_view", r"&\s*self") + r"\s*,\s*"
        + _coverage_call("decomposition_selector_view", "coding_style"),
    ),
    ("src/codestream/coding_style.rs", "Parser::finish_main_component_styles"): (
        "part1_finish_main_styles", _coverage_call("parsed_style_owner_outcome", r"\1"), None,
        r"components\s*,\s*" + _coverage_call("parsed_coding_style_view", "default") + r"\s*,\s*"
        + _coverage_call("segment_slots_view", r"segments@") + r"\s*,\s*&\s*self\.limits\s*,\s*"
        + _coverage_call("owned_extensions_view", "extensions"),
    ),
    ("src/codestream/quantization.rs", "Parser::finish_main_component_quantizations"): (
        "part1_finish_main_quantizations", _coverage_call("parsed_quantization_owner_outcome", r"\1"), None,
        r"components\s*,\s*" + _coverage_call("quantization_view", r"&\s*default") + r"\s*,\s*"
        + _coverage_call("component_style_owner_view", "styles") + r"\s*,\s*"
        + _coverage_call("segment_slots_view", r"segments@"),
    ),
}

_STYLE_OVERRIDE_CONTRACTS = {
    ("src/codestream/coding_style.rs", "Parser::apply_component_style_overrides"): (
        "part1_style_overrides_from", r"\1",
        _coverage_call("component_style_owner_view", _coverage_call("final", "styles")),
        r"components\s*,\s*" + _coverage_call("parsed_coding_style_view", "default") + r"\s*,\s*"
        + _coverage_call("segment_slots_view", r"segments@") + r"\s*,\s*&\s*self\.limits\s*,\s*"
        + _coverage_call("component_style_owner_view", _coverage_call("old", "styles")) + r"\s*,\s*0",
    ),
}

_QUANTIZATION_OVERRIDE_CONTRACTS = {
    ("src/codestream/quantization.rs", "Parser::apply_component_quantization_overrides"): (
        "part1_quantization_overrides_from", r"\1",
        _coverage_call("parsed_quantization_owner_view", _coverage_call("final", "quantizations")),
        r"components\s*,\s*" + _coverage_call("component_style_owner_view", "styles") + r"\s*,\s*"
        + _coverage_call("segment_slots_view", r"segments@") + r"\s*,\s*"
        + _coverage_call("parsed_quantization_owner_view", _coverage_call("old", "quantizations"))
        + r"\s*,\s*0",
    ),
}

_TILE_COMPONENT_FINALIZATION_CONTRACTS = {
    ("src/codestream/tiles.rs", "Parser::finish_tile_component_configuration"): (
        "part1_finish_tile_components", _coverage_call("tile_component_configuration_outcome", r"\1"), None,
        r"components\s*,\s*" + _coverage_call("parsed_coding_style_view", "tile_coding_style")
        + r"\s*,\s*tile_cod_seen\s*,\s*" + _coverage_call("segment_slots_view", r"coc_segments@")
        + r"\s*,\s*" + _coverage_call("optional_segment_view", "qcd_segment")
        + r"\s*,\s*" + _coverage_call("quantization_view", r"&\s*default_quantization")
        + r"\s*,\s*" + _coverage_call("segment_slots_view", r"qcc_segments@")
        + r"\s*,\s*" + _coverage_call("component_style_owner_view", r"&\s*inherited_coding_styles")
        + r"\s*,\s*" + _coverage_call("parsed_quantization_owner_view", r"&\s*inherited_quantizations")
        + r"\s*,\s*" + _coverage_call("owned_extensions_view", "part2_extensions")
        + r"\s*,\s*&\s*self\.limits",
    ),
}

_TILE_HEADER_ADMISSION_CONTRACTS = {
    ("src/codestream/reader.rs", "Parser::read_tile_header_segment"): (
        "part1_read_tile_header_segment", _coverage_call("main_header_segment_outcome", r"\1"),
        _coverage_call("parser_view", _coverage_call("final", "self")),
        _coverage_call("parser_view", _coverage_call("old", "self")),
    ),
}

_RAW_TILE_HEADER_CONTRACTS = {
    ("src/codestream/tile_header_traversal.rs", "new_tile_header_accumulator"): (
        "part1_tile_header_initial", _coverage_call("tile_header_accumulator_view", r"&\s*\1"), None,
        r"start\s*,\s*" + _coverage_call("parsed_coding_style_view", "style") + r"\s*,\s*"
        + _coverage_call("roi_shifts_view", r"&\s*roi") + r"\s*,\s*"
        + _coverage_call("progression_changes_view", r"&\s*progression") + r"\s*,\s*"
        + _coverage_call("mct_parameters_view", r"&\s*mct") + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", r"&\s*extensions"),
    ),
    ("src/codestream/tile_header_traversal.rs", "Parser::read_tile_header"): (
        "part1_read_tile_header",
        _coverage_call("tile_header_read_outcome", r"\1"),
        _coverage_call("parser_view", _coverage_call("final", "self")),
        _coverage_call("parser_view", _coverage_call("old", "self")) + r"\s*,\s*"
        + _coverage_call("parsed_coding_style_view", "style") + r"\s*,\s*"
        + _coverage_call("roi_shifts_view", r"&\s*roi") + r"\s*,\s*"
        + _coverage_call("progression_changes_view", r"&\s*progression") + r"\s*,\s*"
        + _coverage_call("mct_parameters_view", r"&\s*mct") + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", r"&\s*extensions")
        + r"\s*,\s*components\s*,\s*tile_part_index\s*,\s*"
        + _coverage_call("packet_lengths_view", r"&\s*main_lengths") + r"\s*,\s*"
        + _coverage_call("packed_packet_headers_view", r"&\s*main_headers"),
    ),
}
for _tile_symbol, _tile_model, _tile_arguments in (
    ("dispatch_tile_header_segment", "part1_tile_header_dispatch",
     _coverage_call("segment_view", "segment")
     + r"\s*,\s*components\s*,\s*tile_part_index\s*,\s*"
     + _coverage_call("packet_lengths_view", r"&\s*main_lengths") + r"\s*,\s*"
     + _coverage_call("packed_packet_headers_view", r"&\s*main_headers")),
    ("apply_tile_header_segment", "part1_tile_header_payload",
     _coverage_call("segment_view", "segment")
     + r"\s*,\s*components\s*,\s*tile_part_index\s*,\s*"
     + _coverage_call("packet_lengths_view", r"&\s*main_lengths") + r"\s*,\s*"
     + _coverage_call("packed_packet_headers_view", r"&\s*main_headers")),
    ("apply_tile_header_extension_segment", "part1_tile_header_extension_payload",
     _coverage_call("segment_view", "segment") + r"\s*,\s*components"),
    ("apply_tile_header_packet_segment", "part1_tile_header_packet_payload",
     _coverage_call("segment_view", "segment") + r"\s*,\s*"
     + _coverage_call("packet_lengths_view", r"&\s*main_lengths") + r"\s*,\s*"
     + _coverage_call("packed_packet_headers_view", r"&\s*main_headers")),
    ("apply_tile_header_mct_segment", "part1_tile_header_mct_payload",
     _coverage_call("segment_view", "segment") + r"\s*,\s*components"),
    ("traverse_tile_header", "part1_traverse_tile_header",
     r"components\s*,\s*tile_part_index\s*,\s*"
     + _coverage_call("packet_lengths_view", r"&\s*main_lengths") + r"\s*,\s*"
     + _coverage_call("packed_packet_headers_view", r"&\s*main_headers")),
):
    _RAW_TILE_HEADER_CONTRACTS[
        ("src/codestream/tile_header_traversal.rs", "Parser::" + _tile_symbol)
    ] = (
        _tile_model, r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self")) + r"\s*,\s*"
        + _coverage_call("tile_header_accumulator_view", _coverage_call("final", "raw")),
        _coverage_call("parser_view", _coverage_call("old", "self")) + r"\s*,\s*"
        + _coverage_call("tile_header_accumulator_view", _coverage_call("old", "raw"))
        + r"\s*,\s*" + _tile_arguments,
    )

_ROI_SETTER_CONTRACTS = {
    ("src/codestream/quantization.rs", "RoiShifts::set"): (
        "part1_set_roi_shift", r"\1",
        _coverage_call("roi_shifts_view", _coverage_call("final", "self")),
        _coverage_call("roi_shifts_view", _coverage_call("old", "self"))
        + r"\s*,\s*component\s*,\s*shift",
    ),
}

_COMPONENT_SEGMENT_ADMISSION_CONTRACTS = {
    ("src/codestream/coding_markers.rs", "Parser::record_component_segment"): (
        "part1_record_component_segment", r"\1",
        _coverage_call("segment_slots_view", _coverage_call("final", "segments") + "@")
        + r"\s*,\s*" + _coverage_call("parser_view", "self"),
        _coverage_call("parser_view", "self") + r"\s*,\s*"
        + _coverage_call("segment_view", "segment") + r"\s*,\s*components\s*,\s*invalid_kind\s*,\s*"
        + _coverage_call("segment_slots_view", _coverage_call("old", "segments") + "@"),
    ),
}

_COMPONENT_SEGMENT_ADMISSION_CALLERS = {
    ("src/codestream/layout.rs", "Parser::parse_layout"): ("parser", r"image_size\.components", ""),
    ("src/codestream/tiles.rs", "Parser::read_tile_part"): ("self", "components", ""),
    ("src/codestream/tile_header_traversal.rs", "Parser::apply_tile_header_segment"): (
        "self", "components", r"raw\.",
    ),
}

# Keep this boundary out of component-stage relays: a tile path must not
# satisfy a missing main-header producer edge from the same layout caller.
_TILE_PART_READER_CONTRACTS = {
    ("src/codestream/tiles.rs", "Parser::read_tile_part"): (
        "part1_read_tile_part", _coverage_call("tile_part_read_outcome", r"\1"),
        _coverage_call("parser_view", _coverage_call("final", "self")),
        _coverage_call("parser_view", _coverage_call("old", "self")) + r"\s*,\s*"
        + _coverage_call("tile_part_header_view", "tile_part") + r"\s*,\s*\(\s*"
        + _coverage_call("parsed_coding_style_view", r"default_parameters\.0") + r"\s*,\s*"
        + _coverage_call("quantization_view", r"&\s*default_parameters\.1") + r"\s*\)\s*,\s*"
        + _coverage_call("component_style_owner_view", r"&\s*inherited_coding_styles") + r"\s*,\s*"
        + _coverage_call("parsed_quantization_owner_view", r"&\s*inherited_quantizations") + r"\s*,\s*"
        + _coverage_call("roi_shifts_view", r"&\s*inherited_roi_shifts") + r"\s*,\s*"
        + _coverage_call("progression_changes_view", r"&\s*inherited_progression_changes") + r"\s*,\s*"
        + _coverage_call("mct_parameters_view", r"&\s*mct_parameters") + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", r"&\s*part2_extensions") + r"\s*,\s*components\s*,\s*"
        + _coverage_call("packet_lengths_view", r"&\s*main_packet_lengths") + r"\s*,\s*"
        + _coverage_call("packed_packet_headers_view", r"&\s*main_packed_packet_headers"),
    ),
}

_PERSISTENT_TILE_CONFIGURATION_FIELDS = (
    "roi", "styles", "quantizations", "style_parts", "component_quantizations", "progression",
)

_PERSISTENT_TILE_CONFIGURATION_CONTRACTS = {
    ("src/codestream/persistent_tile_configuration.rs", "Parser::commit_persistent_tile_configuration"): (
        "part1_commit_persistent_tile_configuration", r"\1",
        _coverage_call("persistent_tile_configuration_view", *(
            _coverage_call("final", name) for name in _PERSISTENT_TILE_CONFIGURATION_FIELDS
        )),
        r"self\.position\s*,\s*start\s*,\s*index\s*,\s*payload_index\s*,\s*"
        + _coverage_call("optional_roi_shifts_view", "previous_roi") + r"\s*,\s*"
        + _coverage_call("tile_part_payload_view", "payload") + r"\s*,\s*"
        + _coverage_call("persistent_tile_configuration_view", *(
            _coverage_call("old", name) for name in _PERSISTENT_TILE_CONFIGURATION_FIELDS
        )),
    ),
    ("src/codestream/quantization.rs", "RoiShifts::equals"): (
        "part1_roi_shifts_equal", r"\1", None,
        _coverage_call("roi_shifts_view", "self") + r"\s*,\s*"
        + _coverage_call("roi_shifts_view", "other"),
    ),
}

_INHERITED_TILE_CONFIGURATION_CONTRACTS = {
    ("src/codestream/persistent_tile_configuration.rs", "Parser::select_inherited_tile_configuration"): (
        "part1_select_inherited_tile_configuration",
        _coverage_call("inherited_tile_configuration_outcome", r"\1"), None,
        r"self\.position\s*,\s*index\s*,\s*"
        + _coverage_call("roi_shifts_view", "main_roi") + r"\s*,\s*"
        + _coverage_call("parsed_coding_style_view", r"\*\s*main_style") + r"\s*,\s*"
        + _coverage_call("quantization_view", "main_quantization") + r"\s*,\s*"
        + _coverage_call("component_style_owner_view", "main_components") + r"\s*,\s*"
        + _coverage_call("persistent_tile_selection_view",
                         "roi", "styles", "quantizations", "style_parts", "payloads"),
    ),
}

_MCT_PARAMETER_CLONE_CONTRACTS = {
    ("src/codestream/mct.rs", "MctParameters::clone"): (
        "part1_mct_parameters_copy", _coverage_call("mct_parameter_copy_view", r"&\s*\1"),
        None, _coverage_call("mct_parameter_copy_view", "self"),
    ),
    ("src/codestream/mct.rs", "MctRecord::clone"): (
        "part1_mct_record_copy", _coverage_call("mct_record_view", r"&\s*\1"),
        None, _coverage_call("mct_record_view", "self"),
    ),
    ("src/codestream/mct.rs", "MctCollectionReference::clone"): (
        "part1_mcc_collection_reference_copy",
        _coverage_call("mcc_collection_reference_view", r"&\s*\1"),
        None, _coverage_call("mcc_collection_reference_view", "self"),
    ),
}

_MCT_PARAMETER_CLONE_CONSUMERS = (
    ("src/codestream/layout.rs", "Parser::parse_layout",
     r"(?:let\s+inherited_mct_parameters\s*=\s*match\s+"
     + _coverage_call("tile_mct_parameters.get", "tile_index")
     + r"\s*\{\s*Some\s*\(\s*Some\s*\(\s*parameters\s*\)\s*\)\s*=>\s*"
     + _coverage_call("parameters.clone") + r"\s*,\s*_\s*=>\s*"
     + _coverage_call("main_mct_parameters.clone") + r"\s*,?\s*\}\s*;"
     + r"|let\s+inherited_mct_parameters\s*=\s*"
     + _coverage_call("inherited_tile_owner", "tile_index",
                      r"&\s*main_mct_parameters", r"&\s*tile_mct_parameters\s*,?")
     + r"\s*\.\s*" + _coverage_call("clone") + r"\s*;)"),
    ("src/codestream/mct.rs", "MctParameters::clone",
     _coverage_call("Clone::clone", r"&\s*self\.records")),
    ("src/codestream/mct.rs", "MctRecord::clone",
     _coverage_call("Clone::clone", r"&\s*self\.collections")),
)

_OWNED_TILE_INHERITANCE_CONTRACTS = {
    ("src/codestream/persistent_tile_configuration.rs", "inherited_tile_owner"): (
        "part1_inherited_tile_owner", r"\*\s*\1", None,
        r"index\s*,\s*\*\s*main\s*,\s*states\s*@",
    ),
}

_OWNED_TILE_INHERITANCE_FIELDS = (
    ("inherited_component_quantizations", "component_quantizations",
     "tile_component_quantizations", "quantization_owner_view"),
    ("inherited_progression_changes", "progression_changes",
     "tile_progression_changes", "progression_changes_view"),
    ("inherited_mct_parameters", "main_mct_parameters",
     "tile_mct_parameters", "mct_parameter_copy_view"),
    ("inherited_part2_extensions", "part2_extensions",
     "tile_part2_extensions", "owned_extensions_view"),
)

_PERSISTENT_TILE_STATE_FIELDS = (
    "tile_roi_shifts", "tile_coding_styles", "tile_quantizations",
    "tile_component_style_parts", "tile_component_quantizations",
    "tile_progression_changes", "tile_mct_parameters", "tile_part2_extensions",
    "tile_part_payloads",
)

_COMPONENT_PRODUCER_RELAYS = {
    **_MAIN_COMPONENT_FINALIZATION_CONTRACTS,
    **_STYLE_OVERRIDE_CONTRACTS,
    **_QUANTIZATION_OVERRIDE_CONTRACTS,
    **_TILE_COMPONENT_FINALIZATION_CONTRACTS,
    **_COMPONENT_SEGMENT_ADMISSION_CONTRACTS,
    **_TILE_HEADER_ADMISSION_CONTRACTS,
    **_RAW_TILE_HEADER_CONTRACTS,
}

_DECOMPOSITION_RESOLUTION_CONTRACTS = {
    ("src/codestream/extensions.rs", "Part2Extensions::decomposition_structure"): (
        "part1_dfs_lookup", _coverage_call("dfs_option_view", r"\1"), None,
        _coverage_call("owned_extensions_view", "self") + r"\.decompositions\s*,\s*index\s*,\s*0",
    ),
    ("src/codestream/extensions.rs", "Part2Extensions::arbitrary_decomposition"): (
        "part1_ads_lookup", _coverage_call("ads_option_view", r"\1"), None,
        _coverage_call("owned_extensions_view", "self") + r"\.arbitrary\s*,\s*index\s*,\s*0",
    ),
    ("src/codestream/coding_style.rs", "ComponentCodingStyles::set"): (
        "part1_set_component_style", r"\1",
        _coverage_call("component_style_owner_view", _coverage_call("final", "self")),
        _coverage_call("component_style_owner_view", _coverage_call("old", "self"))
        + r"\s*,\s*component\s*,\s*" + _coverage_call("parsed_coding_style_view", "style"),
    ),
    ("src/codestream/decomposition.rs", "resolve_decomposition_style"): (
        "part1_resolve_decomposition_style", _coverage_call("parsed_coding_style_outcome", r"\1"), None,
        _coverage_call("parsed_coding_style_view", "style")
        + r"\s*,\s*" + _coverage_call("owned_extensions_view", "extensions"),
    ),
    ("src/codestream/decomposition.rs", "Parser::resolve_decomposition_structures"): (
        "part1_resolve_decompositions", r"\1",
        _coverage_call("component_style_owner_view", _coverage_call("final", "styles")),
        _coverage_call("component_style_owner_view", _coverage_call("old", "styles"))
        + r"\s*,\s*" + _coverage_call("owned_extensions_view", "extensions"),
    ),
}

_DECOMPOSITION_BYTES_CONTRACTS = {
    ("src/codestream/decomposition.rs", "Parser::unpack_two_bit_values"): (
        "part1_unpack_two_bit_values", _coverage_call("two_bit_values_outcome", r"\1"), None,
        r"self\.position\s*,\s*" + _coverage_call("segment_view", "segment")
        + r"\s*,\s*start\s*,\s*count\s*,\s*allow_terminal",
    ),
    ("src/codestream/decomposition.rs", "Parser::decode_dfs_payload"): (
        "part1_dfs_payload", _coverage_call("dfs_payload_outcome", r"\1"), None,
        _coverage_call("segment_view", "segment"),
    ),
    ("src/codestream/decomposition.rs", "Parser::decode_ads_payload"): (
        "part1_ads_payload", _coverage_call("ads_payload_outcome", r"\1"), None,
        r"self\.position\s*,\s*" + _coverage_call("segment_view", "segment"),
    ),
    ("src/codestream/decomposition.rs", "Parser::parse_dfs"): (
        "part1_parse_dfs", r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self")) + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("final", "extensions")),
        _coverage_call("parser_view", _coverage_call("old", "self")) + r"\s*,\s*"
        + _coverage_call("segment_view", "segment") + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("old", "extensions")),
    ),
    ("src/codestream/decomposition.rs", "Parser::parse_ads"): (
        "part1_parse_ads", r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self")) + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("final", "extensions")),
        _coverage_call("parser_view", _coverage_call("old", "self")) + r"\s*,\s*"
        + _coverage_call("segment_view", "segment") + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("old", "extensions")),
    ),
}

_COMPONENT_MARKER_BYTES_CONTRACTS = {
    ("src/limits.rs", "ResourceLimits::maximum_metadata_bytes"): (
        "part1_metadata_byte_limit", r"\1", None, "self",
    ),
    ("src/codestream/reader.rs", "Parser::segment_byte"): (
        "part1_segment_byte", r"\1", None,
        r"self\.position\s*,\s*" + _coverage_call("segment_view", "segment")
        + r"\s*,\s*position\s*,\s*relative",
    ),
    ("src/codestream/reader.rs", "Parser::charge_extension_metadata"): (
        "part1_charge_extension_metadata", r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self")) + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("final", "extensions")),
        _coverage_call("parser_view", _coverage_call("old", "self")) + r"\s*,\s*"
        + _coverage_call("segment_view", "segment") + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("old", "extensions")),
    ),
    ("src/codestream/image_header.rs", "Parser::parse_crg"): (
        "part1_parse_crg", r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self")) + r"\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("final", "extensions")),
        _coverage_call("parser_view", _coverage_call("old", "self")) + r"\s*,\s*"
        + _coverage_call("segment_view", "segment") + r"\s*,\s*components\s*,\s*"
        + _coverage_call("owned_extensions_view", _coverage_call("old", "extensions")),
    ),
    ("src/codestream/coding_markers.rs", "Parser::parse_rgn"): (
        "part1_parse_rgn", r"\1", None,
        r"segment\.offset\s*,\s*segment\.payload\s*@\s*,\s*components",
    ),
}

_QUANTIZATION_BYTES_CONTRACTS = {
    ("src/codestream/coding_markers.rs", "Parser::parse_qcd"): (
        "part1_parse_qcd_payload", _coverage_call("parsed_quantization_outcome", r"\1"), None,
        r"segment\.offset\s*,\s*segment\.payload\s*@\s*,\s*"
        + _coverage_call("parsed_coding_style_view", "coding_style"),
    ),
    ("src/codestream/coding_markers.rs", "Parser::parse_qcd_payload"): (
        "part1_parse_qcd_payload", _coverage_call("parsed_quantization_outcome", r"\1"), None,
        r"segment_offset\s*,\s*payload\s*@\s*,\s*"
        + _coverage_call("parsed_coding_style_view", "coding_style"),
    ),
    ("src/codestream/coding_markers.rs", "Parser::parse_qcc"): (
        "part1_parse_qcc", _coverage_call("parsed_component_quantization_outcome", r"\1"), None,
        r"segment\.offset\s*,\s*segment\.payload\s*@\s*,\s*components\s*,\s*"
        + _coverage_call("parsed_coding_style_view", "coding_style"),
    ),
}

_ORDINARY_PRECINCT_CONTRACTS = {
    ("src/codestream/coding_markers.rs", "Parser::validate_ordinary_precincts"): (
        "part1_validate_ordinary_precincts", r"\1", None,
        r"segment_offset\s*,\s*style\.decomposition_structure\s*,\s*style\.precincts_defined\s*,\s*"
        r"style\.decomposition_levels\s*,\s*style\.precinct_exponents\s*@",
    ),
}
_COMPONENT_STYLE_BYTES_CONTRACTS = {
    ("src/codestream/coding_markers.rs", "Parser::prepare_coc_payload"): (
        "part1_coc_prepare", _coverage_call("parsed_component_coding_style_payload_outcome", r"\1"), None,
        r"segment\.offset\s*,\s*segment\.payload\s*@\s*,\s*components\s*,\s*"
        + _coverage_call("parsed_coding_style_view", "default"),
    ),
    ("src/codestream/coding_markers.rs", "Parser::parse_component_index"): (
        "part1_parse_component_index", r"\1", None,
        r"segment\.offset\s*,\s*segment\.payload\s*@\s*,\s*components\s*,\s*invalid_kind",
    ),
    ("src/codestream/coding_markers.rs", "Parser::parse_coc"): (
        "part1_parse_coc", _coverage_call("parsed_component_coding_style_outcome", r"\1"), None,
        r"segment\.offset\s*,\s*segment\.payload\s*@\s*,\s*components\s*,\s*"
        + _coverage_call("parsed_coding_style_view", "default") + r"\s*,\s*self\.limits",
    ),
} | _ORDINARY_PRECINCT_CONTRACTS

_CODING_STYLE_BYTES_CONTRACTS = {
    ("src/codestream/coding_markers.rs", "Parser::parse_cod"): (
        "part1_parse_cod", _coverage_call("parsed_coding_style_outcome", r"\1"), None,
        r"segment\.offset\s*,\s*segment\.payload\s*@\s*,\s*self\.limits",
    ),
    ("src/codestream/coding_markers.rs", "Parser::parse_cod_payload"): (
        "part1_parse_cod_payload", _coverage_call("parsed_coding_style_outcome", r"\1"), None,
        r"segment_offset\s*,\s*payload\s*@\s*,\s*self\.limits",
    ),
} | _ORDINARY_PRECINCT_CONTRACTS

_MAIN_HEADER_ADMISSION_CONTRACTS = {
    ("src/codestream/reader.rs", "Parser::read_main_header_segment"): (
        "part1_read_main_header_segment", _coverage_call("main_header_segment_outcome", r"\1"),
        _coverage_call("parser_view", _coverage_call("final", "self"))
        + r"\s*,\s*\*\s*" + _coverage_call("final", "main_header_segments"),
        _coverage_call("parser_view", _coverage_call("old", "self"))
        + r"\s*,\s*\*\s*" + _coverage_call("old", "main_header_segments"),
    ),
}

_LAYOUT_PROLOGUE_CONTRACTS = {
    ("src/codestream/layout.rs", "Parser::parse_layout_prologue"): (
        "part1_parse_layout_prologue", _coverage_call("layout_prologue_outcome", r"\1"),
        _coverage_call("parser_view", _coverage_call("final", "self")),
        _coverage_call("parser_view", _coverage_call("old", "self")),
    ),
}

_TILE_LOOP_CONTRACTS = {
    ("src/codestream/layout.rs", "Parser::tile_part_main_metadata"): (
        "part1_tile_part_main_metadata", _coverage_call("tile_part_main_metadata_outcome", r"\1"), None,
        r"self\.position\s*,\s*" + _coverage_call("tile_part_header_view", "tile_part")
        + r"\s*,\s*part_index\s*,\s*lengths\s*@\s*,\s*plm_seen\s*,\s*"
        + _coverage_call("packet_length_groups_view", r"plm_groups\s*@") + r"\s*,\s*"
        + _coverage_call("packed_header_frames_view", r"ppm_frames\s*@")
        + r"\s*,\s*ppm_fragments\s*,\s*main_header\s*@",
    ),
    ("src/codestream/layout.rs", "Parser::finish_tile_part_traversal"): (
        "part1_finish_tile_part_traversal", r"\1",
        _coverage_call("parser_view", _coverage_call("final", "self")),
        _coverage_call("parser_view", _coverage_call("old", "self"))
        + r"\s*,\s*tile_parts\s*,\s*plm_seen\s*,\s*plm_count\s*,\s*"
        r"ppm_fragments\s*,\s*ppm_count\s*,\s*tlm_count",
    ),
}

_SIZ_GEOMETRY_CONTRACTS = {
    ("src/codestream/image_header.rs", "Parser::parse_siz"): (
        "part1_parse_siz", _coverage_call("parsed_siz_outcome", r"\1"), None,
        _coverage_call("segment_view", "segment") + r"\s*,\s*self\.limits",
    ),
    ("src/codestream/reader.rs", "Parser::malformed_at"): (
        "part1_codestream_malformed", r"\1", None, r"value\s*,\s*kind",
    ),
    ("src/codestream/reader.rs", "read_u32"): (
        "part1_codestream_u32", r"\1", None,
        r"bytes\s*\[\s*0\s*\]\s*,\s*bytes\s*\[\s*1\s*\]\s*,\s*bytes\s*\[\s*2\s*\]\s*,\s*bytes\s*\[\s*3\s*\]",
    ),
    ("src/codestream/geometry.rs", "ceil_div"): (
        "part1_image_ceil_div", r"\1", None, r"value\s*,\s*divisor",
    ),
}

_TILE_DATA_WINDOW_CONTRACTS = {
    ("src/codestream/tiles.rs", "Parser::tile_data_window"): (
        "part1_tile_data_window", _coverage_call("tile_data_window_outcome", r"\1"),
        _coverage_call("parser_view", _coverage_call("final", "self")),
        _coverage_call("parser_view", _coverage_call("old", "self"))
        + r"\s*,\s*data_start\s*,\s*start\s*,\s*length",
    ),
}

_CODESTREAM_READER_CONTRACTS = {
    ("src/codestream/reader.rs", "new_parser"): (
        "part1_codestream_reader_new", _coverage_call("parser_initial_outcome", r"\1"), None, r"input\s*@\s*,\s*limits",
    ),
    ("src/codestream/reader.rs", "Parser::peek_marker"): (
        "part1_codestream_peek_marker", r"\1", None, _coverage_call("parser_view", "self"),
    ),
    ("src/codestream/reader.rs", "Parser::expect_standalone"): (
        "part1_codestream_expect_standalone", r"\1", _coverage_call("parser_view", _coverage_call("final", "self")),
        _coverage_call("parser_view", _coverage_call("old", "self")) + r"\s*,\s*expected",
    ),
    ("src/codestream/reader.rs", "Parser::read_segment"): (
        "part1_codestream_read_segment", _coverage_call("segment_outcome", r"\1"),
        _coverage_call("parser_view", _coverage_call("final", "self")),
        _coverage_call("parser_view", _coverage_call("old", "self")),
    ),
    ("src/codestream/tiles.rs", "Parser::find_eoc"): (
        "part1_codestream_find_eoc", r"\1", _coverage_call("parser_view", _coverage_call("final", "self")),
        _coverage_call("parser_view", _coverage_call("old", "self")),
    ),
    ("src/codestream/reader.rs", "Parser::charge_work"): (
        "part1_codestream_charge_work", r"\1", _coverage_call("parser_view", _coverage_call("final", "self")),
        _coverage_call("parser_view", _coverage_call("old", "self")) + r"\s*,\s*amount",
    ),
    ("src/codestream/reader.rs", "Parser::malformed_here"): (
        "part1_codestream_malformed", r"\1", None, r"self\.position\s*,\s*kind",
    ),
    ("src/codestream/reader.rs", "Parser::offset"): (
        "part1_codestream_offset", r"\1", None, r"value",
    ),
    ("src/codestream/reader.rs", "is_standalone_marker"): (
        "part1_codestream_standalone", r"\1", None, r"marker",
    ),
    ("src/codestream/reader.rs", "read_u16"): (
        "part1_marker_value", r"\1", None, r"bytes\s*\[\s*0\s*\]\s*,\s*bytes\s*\[\s*1\s*\]",
    ),
}

_SOT_READER_CONTRACTS = {
    ("src/codestream/tiles.rs", "Parser::read_sot"): (
        "part1_codestream_read_sot", _coverage_call("tile_part_header_outcome", r"\1"),
        _coverage_call("parser_view", _coverage_call("final", "self")),
        _coverage_call("parser_view", _coverage_call("old", "self")) + r"\s*,\s*tile_count",
    ),
    ("src/codestream/reader.rs", "is_known_segment_marker"): (
        "part1_known_segment_marker", r"\1", None, r"marker",
    ),
    ("src/codestream/reader.rs", "is_allowed_main_header"): (
        "part1_allowed_main_header", r"\1", None, r"marker",
    ),
    ("src/codestream/reader.rs", "is_allowed_tile_header"): (
        "part1_allowed_tile_header", r"\1", None, r"marker",
    ),
}

_TYPED_LAYOUT_CONTRACTS = {
    ("src/decode/api.rs", "typed_layout"): (
        "part2_typed_layout", _coverage_call("crate::image::decoded_typed_image_outcome", r"\1"), None,
        r"layout\s*,\s*" + _coverage_call("crate::image::decoded_image_view", "decoded") + r"\s*,\s*discard_levels\s*,\s*limits",
    ),
    ("src/decode/api.rs", "decode_typed_layout"): (
        "part2_decode_typed_layout", _coverage_call("crate::image::decoded_typed_image_outcome", r"\1"), None,
        r"input_bytes\s*,\s*layout\s*,\s*limits\s*,\s*requested",
    ),
}

_RAW_TYPED_ENTRY = "part2-complete-native-raw-codestream-typed-result"
_RAW_RECOVERY_ENTRY = "implementation-raw-missing-eoc-recovery"
_RAW_RECOVERY_CONTRACTS = {
    ("src/codestream/recovery_framing.rs", "recovery_framing"): (
        "raw_recovery_framing", _coverage_call("framing_outcome", r"\1"), None, r"input@\s*,\s*limits",
    ),
    **{
        ("src/codestream/recovery_framing.rs", "Parser::" + name): (
            model, _coverage_call("framing_outcome", r"\1"),
            _coverage_call("parser_view", _coverage_call("final", "self")),
            _coverage_call("parser_view", _coverage_call("old", "self")) + suffix,
        )
        for name, model, suffix in (
            ("recovery_main_headers", "raw_recovery_main_headers", r"\s*,\s*1\s*,\s*false\s*,\s*false"),
            ("recovery_sot", "raw_recovery_sot", ""),
            ("recovery_tile_headers", "raw_recovery_tile_headers", ""),
            ("recovery_body", "raw_recovery_body", ""),
        )
    },
    ("src/recovery.rs", "admit_repair"): (
        "raw_recovery_admit", r"\1", None, r"input_bytes\s*,\s*work\s*,\s*limits",
    ),
    ("src/recovery.rs", "finish_recovery"): (
        "raw_recovery_finish", _coverage_call("recovered_outcome", r"\1"), None,
        r"original\s*,\s*\(\s*frame\.append_eoc\s*,\s*frame\.work_units\s*\)\s*,\s*"
        + _coverage_call("crate::image::decoded_typed_image_outcome", "decoded"),
    ),
    ("src/recovery.rs", "recovery_report"): (
        "raw_recovery_report", r"\1", None,
        r"original\s*,\s*\(\s*frame\.append_eoc\s*,\s*frame\.work_units\s*\)\s*,\s*geometry",
    ),
}
_RAW_RECOVERY_RELATIONS = {
    ("src/recovery.rs", "decode_codestream_recover_missing_eoc"): (
        "raw_recovery_result", r"input@\s*,\s*"
        + _coverage_call("crate::options::decode_options_limits", "options") + r"\s*,\s*"
        + _coverage_call("recovered_outcome", r"\1"),
    ),
    ("src/recovery.rs", "append_eoc"): (
        "raw_repair_result", r"input@\s*,\s*" + _coverage_call("repair_outcome", r"\1"),
    ),
}
_RAW_RECONSTRUCTED_ENTRY = "part2-strict-raw-codestream-reconstruction-result"
_RAW_RECONSTRUCTED_CONTRACTS = {
    ("src/decode/api.rs", "decode_codestream_reconstructed"): (
        "part2_decode_raw_reconstructed_codestream",
        _coverage_call("crate::image::decoded_image_outcome", r"\1"), None,
        r"input@\s*,\s*" + _coverage_call("crate::options::decode_options_limits", "options"),
    ),
    ("src/decode/api.rs", "validate_reconstruction_transforms"): (
        "part2_validate_reconstruction_transforms", r"\1", None,
        _coverage_call("codestream::decoder_layout_input_view", "layout"),
    ),
    ("src/decode/api.rs", "validate_reconstructed_output_shape"): (
        "part1_validate_reconstructed_output_shape", r"\1", None,
        r"input_bytes\s*,\s*layout\.tile_parts\.len\(\)\s*,\s*layout\.info\.image_size\.components\s*,\s*"
        + _coverage_call("crate::image::decoded_image_view", r"\*\s*image"),
    ),
}
_RECONSTRUCTED_RECOVERY_ENTRY = "implementation-raw-reconstructed-missing-eoc-recovery"
_RECONSTRUCTED_RECOVERY_CONTRACTS = {
    reference: recipe for reference, recipe in _RAW_RECOVERY_CONTRACTS.items()
    if reference != ("src/recovery.rs", "finish_recovery")
}
_RECONSTRUCTED_RECOVERY_CONTRACTS.update({
    ("src/recovery.rs", "finish_reconstructed_recovery"): (
        "raw_reconstructed_recovery_finish", _coverage_call("reconstructed_recovered_outcome", r"\1"), None,
        r"original\s*,\s*\(\s*frame\.append_eoc\s*,\s*frame\.work_units\s*\)\s*,\s*"
        + _coverage_call("crate::image::decoded_image_outcome", "decoded"),
    ),
    ("src/decode/api.rs", "decode_codestream_reconstructed"):
        _RAW_RECONSTRUCTED_CONTRACTS[("src/decode/api.rs", "decode_codestream_reconstructed")],
})
_RECONSTRUCTED_RECOVERY_RELATIONS = {
    ("src/recovery.rs", "decode_codestream_reconstructed_recover_missing_eoc"): (
        "raw_reconstructed_recovery_result", r"input@\s*,\s*"
        + _coverage_call("crate::options::decode_options_limits", "options") + r"\s*,\s*"
        + _coverage_call("reconstructed_recovered_outcome", r"\1"),
    ),
    ("src/recovery.rs", "append_eoc"): _RAW_RECOVERY_RELATIONS[("src/recovery.rs", "append_eoc")],
}
_RAW_RECOVERY_PUBLIC_ENTRIES = {
    _RAW_RECOVERY_ENTRY: "decode_codestream_recover_missing_eoc",
    _RECONSTRUCTED_RECOVERY_ENTRY: "decode_codestream_reconstructed_recover_missing_eoc",
}
_JPX_SOURCE_ENTRY = "part2-complete-native-jpx-source-image-result"
_JPX_SOURCE_CONTRACTS = {
    ("src/decode/output.rs", "decode_jpx_file"): (
        "part2_decode_jpx_codestream", _coverage_call("associated_typed_outcome", r"\1"), None,
        _coverage_call("jp2::jpx_file_decode_view", "file") + r"\s*,\s*codestream_index\s*,\s*"
        + _coverage_call("crate::options::decode_options_limits", "options"),
    ),
    ("src/decode/api.rs", "decode_codestream"): (
        "part2_decode_raw_codestream", _coverage_call("crate::image::decoded_typed_image_outcome", r"\1"), None,
        r"input@\s*,\s*" + _coverage_call("crate::options::decode_options_limits", "options") + r"\s*,\s*None",
    ),
    ("src/codestream/layout.rs", "parse"): (
        "part1_parse_info", _coverage_call("complete_codestream_info_outcome", r"\1"), None, r"input@\s*,\s*limits",
    ),
    ("src/jp2/container.rs", "associated_header_for_codestream"): (
        "part2_associated_codestream_header", _coverage_call("associated_header_outcome", r"\1"), None,
        _coverage_call("codestream_header_association_view", "selected") + r"\s*,\s*"
        + _coverage_call("associated_header_view", "fallback"),
    ),
    ("src/jp2/container.rs", "validate_selected_header"): (
        "part2_validate_selected_header", r"\1", None,
        r"header\.image\s*,\s*codestream\.image_size\.width\s*,\s*codestream\.image_size\.height\s*,\s*"
        r"codestream\.image_size\.components\s*,\s*codestream\.image_size\.uniform_bit_depth\s*,\s*"
        r"codestream\.image_size\.uniform_signed\s*,\s*offset",
    ),
    ("src/decode/output.rs", "apply_associated_output"): (
        "part2_apply_associated_output", _coverage_call("associated_typed_outcome", r"\1"), None,
        _coverage_call("crate::image::typed_image_value_view", "decoded") + r"\s*,\s*"
        + _coverage_call("jp2::associated_header_option", "header") + r"\s*,\s*"
        + _coverage_call("crate::limits::resource_component_limit", "limits") + r"\s*,\s*"
        + _coverage_call("crate::limits::resource_decoded_bytes_limit", "limits"),
    ),
}
_JPX_LAYER_COLOR_ENTRY = "part2-complete-native-jpx-source-layer-color-result"
_JPX_LAYER_COLOR_CONTRACTS = {
    ("src/jpx/layer_decode.rs", "decode_layer"): (
        "part2_decode_jpx_layer", _coverage_call("crate::color::converted_image_result", r"\1"), None,
        _coverage_call("jp2::jpx_file_decode_view", "file") + r"\s*,\s*codestream_index\s*,\s*"
        + _coverage_call("jp2::optional_color_specification_method", "color_override") + r"\s*,\s*"
        + _coverage_call("crate::options::decode_options_limits", "options"),
    ),
    ("src/decode/output.rs", "decode_jpx_file"):
        _JPX_SOURCE_CONTRACTS[("src/decode/output.rs", "decode_jpx_file")],
    ("src/color/conversion.rs", "convert_jp2_color"): (
        "color_convert_jp2", _coverage_call("converted_image_result", r"\1"), None,
        _coverage_call("crate::image::typed_image_component_views", "image") + r"\s*,\s*"
        + _coverage_call("crate::image::typed_image_definition_views", "image") + r"\s*,\s*"
        + _coverage_call("crate::image::typed_image_geometry", "image") + r"\s*,\s*"
        + _coverage_call("crate::jp2::color_specification_method", "color") + r"\s*,\s*"
        + _coverage_call("crate::limits::resource_decoded_bytes_limit", "limits") + r"\s*,\s*"
        + _coverage_call("crate::limits::resource_work_limit", "limits"),
    ),
}
_RAW_TYPED_CONTRACTS = {
    ("src/decode/api.rs", "decode_codestream"): (
        "part2_decode_raw_codestream", _coverage_call("crate::image::decoded_typed_image_outcome", r"\1"), None,
        r"input@\s*,\s*" + _coverage_call("crate::options::decode_options_limits", "options") + r"\s*,\s*None",
    ),
    ("src/decode/api.rs", "decode_codestream_selected"): (
        "part2_decode_raw_codestream", _coverage_call("crate::image::decoded_typed_image_outcome", r"\1"), None,
        r"input@\s*,\s*" + _coverage_call("crate::options::decode_options_limits", "options")
        + r"\s*,\s*" + _coverage_call("Some", "selection"),
    ),
    **_TYPED_LAYOUT_CONTRACTS,
    ("src/codestream/layout.rs", "parse_layout"): (
        "part1_parse_layout", _coverage_call("complete_layout_outcome", r"\1"), None, r"input@\s*,\s*limits",
    ),
}

_NONLINEAR_APPLICATION_CONTRACTS = {
    ("src/image/nonlinear.rs", "TypedImage::apply_nonlinear_regions"): (
        "part2_apply_nonlinear_regions", r"\1",
        _coverage_call("typed_image_value_view", r"\*\s*" + _coverage_call("final", "self")),
        _coverage_call("typed_image_value_view", r"\*\s*" + _coverage_call("old", "self"))
        + r"\s*,\s*" + _coverage_call("crate::decode::nonlinear_regions_view", "regions@")
        + r"\s*,\s*" + _coverage_call("crate::limits::resource_decoded_bytes_limit", "limits")
        + r"\s*,\s*" + _coverage_call("crate::limits::resource_work_limit", "limits"),
    ),
    ("src/image/nonlinear.rs", "TypedComponent::apply_nonlinear_regions"): (
        "part2_nlt_component_mutation", r"\1",
        _coverage_call("typed_component_view", _coverage_call("final", "self")),
        _coverage_call("typed_component_view", _coverage_call("old", "self")) + r"\s*,\s*component_number\s*,\s*"
        + _coverage_call("crate::decode::nonlinear_regions_view", "regions@")
        + r"\s*,\s*" + _coverage_call("crate::limits::resource_decoded_bytes_limit", "limits")
        + r"\s*,\s*" + _coverage_call("crate::limits::resource_work_limit", "limits") + r"\s*,\s*initial_work",
    ),
}

_NONLINEAR_SCALAR_CONTRACTS = {
    ("src/image/nonlinear_math.rs", "nlt_gamma_parameter"): (
        "part2_nlt_gamma_parameter", r"\1", None, r"raw",
    ),
    ("src/image/nonlinear_math.rs", "nlt_gamma_curve"): (
        "part2_nlt_gamma_curve", r"\1", None,
        r"normalized\s*,\s*exponent\s*,\s*slope\s*,\s*threshold\s*,\s*a\s*,\s*b",
    ),
    ("src/image/nonlinear_math.rs", "inverse_nlt_gamma_sample"): (
        "part2_nlt_gamma_sample", r"\1", None,
        r"source\s*,\s*source_info\s*,\s*" + _coverage_call("crate::codestream::owned_nonlinear_view", "transform"),
    ),
    ("src/image/nonlinear_math.rs", "inverse_nlt_sample"): (
        "part2_nlt_inverse_sample", r"\1", None,
        r"source\s*,\s*source_info\s*,\s*" + _coverage_call("crate::codestream::owned_nonlinear_view", "transform"),
    ),
}

_NONLINEAR_LOG_EXP_CONTRACTS = {
    ("src/image/nonlinear_math.rs", "nlt_ln_normalize"): (
        "part2_nlt_ln_normalize", r"\1", None, r"initial",
    ),
    ("src/image/nonlinear_math.rs", "nlt_ln_series"): (
        "part2_nlt_ln_series", r"\1", None, r"squared\s*,\s*scale\s*,\s*0\s*,\s*initial\s*,\s*0",
    ),
    ("src/image/nonlinear_math.rs", "nlt_fixed_ln_q32"): (
        "part2_nlt_fixed_ln_q32", r"\1", None, r"value",
    ),
    ("src/image/nonlinear_math.rs", "nlt_exp_series"): (
        "part2_nlt_exp_series", r"\1", None, r"remainder\s*,\s*1\s*,\s*4294967296\s*,\s*4294967296",
    ),
    ("src/image/nonlinear_math.rs", "nlt_fixed_exp_q32"): (
        "part2_nlt_fixed_exp_q32", r"\1", None, r"value",
    ),
    ("src/image/nonlinear_math.rs", "nlt_fixed_pow_reciprocal_q32"): (
        "part2_nlt_fixed_pow_reciprocal_q32", r"\1", None, r"base\s*,\s*exponent",
    ),
}

_NONLINEAR_LUT_CONTRACTS = {
    ("src/image/nonlinear_math.rs", "inverse_nlt_lut_sample"): (
        "part2_nlt_lut_sample", r"\1", None,
        r"source\s*,\s*source_info\s*,\s*" + _coverage_call("crate::codestream::owned_nonlinear_view", "transform"),
    ),
    ("src/image/nonlinear_math.rs", "nlt_lut_interpolate_values"): (
        "part2_nlt_lut_interpolate_values", r"\1", None,
        r"left\s*,\s*right\s*,\s*denominator\s*,\s*remainder",
    ),
    ("src/image/nonlinear_math.rs", "nlt_lut_position"): (
        "part2_nlt_lut_position", r"\1", None,
        r"points\s*@\s*,\s*source_scale\s*,\s*nominal\s*,\s*minimum\s*,\s*maximum",
    ),
    ("src/image/nonlinear_math.rs", "nlt_lut_coordinates"): (
        "part2_nlt_lut_coordinates", r"\1", None,
        r"source_scale\s*,\s*nominal\s*,\s*minimum\s*,\s*maximum\s*,\s*last_index\s+as\s+nat",
    ),
    ("src/image/nonlinear_math.rs", "nlt_checked_rem"): (
        "part2_nlt_checked_rem", r"\1", None, r"numerator\s*,\s*denominator",
    ),
}

_NONLINEAR_ARITHMETIC_CONTRACTS = {
    ("src/image/nonlinear_math.rs", "nlt_round_ratio"): (
        "part2_nlt_round_ratio", r"\1", None, r"numerator\s*,\s*denominator",
    ),
    ("src/image/nonlinear_math.rs", "nlt_power_of_two"): (
        "part2_nlt_power_of_two", r"\1", None, r"exponent",
    ),
    ("src/image/nonlinear_math.rs", "nlt_fixed_mul_q32"): (
        "part2_nlt_fixed_mul_q32", r"\1", None, r"left\s*,\s*right",
    ),
    ("src/image/nonlinear_math.rs", "nlt_fixed_div_q32"): (
        "part2_nlt_fixed_div_q32", r"\1", None, r"left\s*,\s*right",
    ),
}

_NONLINEAR_REGIONS_CONTRACTS = {
    ("src/codestream/extensions.rs", "find_nonlinear_transform"): (
        "part2_nonlinear_transform_for_unscoped", _coverage_call("nonlinear_transform_option_view", r"\1"), None,
        _coverage_call("owned_nonlinear_list_view", r"transforms\s*@") + r"\s*,\s*component",
    ),
    ("src/codestream/extensions.rs", "Part2Extensions::nonlinear_transform_for"): (
        "part2_nonlinear_transform_for", _coverage_call("nonlinear_transform_option_view", r"\1"), None,
        _coverage_call("owned_extensions_view", "self") + r"\.nonlinear\s*,\s*component\s*,\s*"
        + _coverage_call("owned_extensions_view", "self") + r"\.nonlinear_local_count",
    ),
    ("src/decode/api.rs", "nonlinear_component_extent"): (
        "part2_nonlinear_component_extent", r"\1", None,
        r"size\s*,\s*" + _coverage_call("crate::image::typed_image_value_view", r"\*\s*image") + r"\s*,\s*component",
    ),
    ("src/decode/api.rs", "collect_nonlinear_regions"): (
        "part2_collect_nonlinear_regions", _coverage_call("nonlinear_regions_outcome", r"\1"), None,
        r"layout\s*,\s*" + _coverage_call("crate::image::typed_image_value_view", r"\*\s*image") + r"\s*,\s*discard_levels",
    ),
}

_OUTPUT_SHAPE_CONTRACTS = {
    ("src/decode/api.rs", "validate_part1_output_shape"): (
        "part1_validate_typed_output_shape", r"\1", None,
        r"input_bytes\s*,\s*layout\.tile_parts\.len\s*\(\s*\)\s*,\s*layout\.info\.image_size\.components\s*,\s*"
        + _coverage_call("crate::image::typed_image_value_view", r"\*\s*image"),
    ),
}

_LAYOUT_DECODING_CONTRACTS = {
    ("src/decode/execution.rs", "decode_layout"): (
        "part2_decode_layout", _coverage_call("crate::image::decoded_image_outcome", r"\1"), None,
        r"layout\s*,\s*limits",
    ),
    ("src/decode/execution.rs", "decode_layout_selected"): (
        "part2_decode_layout_selected", _coverage_call("crate::image::decoded_image_outcome", r"\1"), None,
        r"layout\s*,\s*requested\s*,\s*limits",
    ),
}

_TILE_COLLECTION_CONTRACTS = {
    ("src/codestream/tiles.rs", "TilePartPayload::clone"): (
        "part2_tile_part_copy", _coverage_call("tile_part_owned_view", r"&\s*\1"), None,
        _coverage_call("tile_part_owned_view", "self"),
    ),
    ("src/decode/execution.rs", "collect_tile_parts"): (
        "part2_collect_tile_parts", _coverage_call("collected_tile_parts_outcome", r"\1"), None,
        _coverage_call("codestream::tile_parts_owned_view", "parts@") + r"\s*,\s*tile",
    ),
}

_RAW_TILE_DECODING_CONTRACTS = {
    ("src/decode/execution.rs", "decode_tile_parts_at"): (
        "part2_decode_tile_parts_at", _coverage_call("decoded_layout_tile_outcome", r"\1"), None,
        r"size\s*,\s*tile\s*,\s*parts@\s*,\s*" + _coverage_call("codestream::codestream_profile_capabilities", "profile")
        + r"\s*,\s*discard\s*,\s*limits\s*,\s*" + _coverage_call("prepared_components_view", "prepared@")
        + r"\s*,\s*initial\s*,\s*mct_work",
    ),
}

_MAIN_HEADER_INITIALIZER_CONTRACTS = {
    ("src/codestream/coding_style.rs", "new_progression_changes"): (
        "part1_empty_progression_changes", _coverage_call("progression_changes_view", r"&\s*\1"), None, "",
    ),
    ("src/codestream/quantization.rs", "new_roi_shifts"): (
        "part1_empty_roi_shifts", _coverage_call("roi_shifts_view", r"&\s*\1"), None, "",
    ),
    ("src/codestream/extensions.rs", "new_part2_extensions"): (
        "part1_empty_extensions", _coverage_call("owned_extensions_view", r"&\s*\1"), None, "",
    ),
}

_MAIN_HEADER_LAYOUT = ("src/codestream/layout.rs", "Parser::parse_layout")
_RAW_LAYOUT_WRAPPER_BODY = (
    r"\s*(?:#\[\s*cfg\s*\(\s*verus_keep_ghost\s*\)\s*\]\s*proof!\s*\{\s*"
    + _coverage_call("reveal", "complete_layout_outcome") + r"\s*;\s*"
    + _coverage_call("reveal", "parser_initial_outcome") + r"\s*;\s*"
    + _coverage_call("crate::specs::part1_parse_layout_unfold", "input@", "limits")
    + r"\s*;\s*\}\s*)?" + _coverage_call("new_parser", "input", "limits")
    + r"\s*\?\s*\.\s*" + _coverage_call("parse_layout") + r"\s*"
)
_RAW_LAYOUT_ENTRY = "part1-complete-native-raw-layout-result"
_RAW_LAYOUT_CONTRACTS = {
    ("src/codestream/layout.rs", "parse"): (
        "part1_parse_info", _coverage_call("complete_codestream_info_outcome", r"\1"), None, r"input@\s*,\s*limits",
    ),
    ("src/codestream/layout.rs", "parse_layout"): (
        "part1_parse_layout", _coverage_call("complete_layout_outcome", r"\1"), None, r"input@\s*,\s*limits",
    ),
    _MAIN_HEADER_LAYOUT: (
        "part1_read_layout", _coverage_call("complete_layout_outcome", r"\1"), None,
        _coverage_call("parser_view", r"&\s*self"),
    ),
}
_RAW_ROI_PREDICATE = (
    r"(?:#\[\s*cfg_attr\s*\(\s*verus_keep_ghost\s*,\s*verus_spec\s*\(\s*"
    r"result\s*:\s*bool\s*=>\s*ensures\s+result\s*==\s*\*\s*seen\s*,?\s*\)\s*\)\s*\]\s*)?"
    r"\|\s*seen\s*\|\s*\*\s*seen\s*,?"
)
_MAIN_HEADER_RAW_ARGUMENTS = (
    r"&\s*image_size", "r_siz", "main_header_start", "main_header_segments",
    "coding_style", "qcd_segment", "coc_segments@", "qcc_segments@", r"&\s*roi_shifts", "roi_seen@",
    "plm_groups@", "next_plm_index", "plm_seen", "ppm_bytes@", "next_ppm_index", "ppm_fragments",
    r"&\s*progression_changes", "poc_seen", "mct_arrays@", "mct_records@", r"&\s*mct_order",
    "pending_mct@", "completed_mct@", "pending_mcc@", "completed_mcc@",
    r"&\s*extended_capabilities", r"&\s*profile", r"&\s*corresponding_profile",
    r"&\s*part2_extensions", "next_tlm_index",
)

_PROFILE_RESULT_CONTRACTS = {
    ("src/codestream/profile.rs", "classify_codestream_profile"): (
        "part1_classify_codestream_profile", _coverage_call("complete_codestream_profile_outcome", r"\1"), None,
        r"r_siz\s*,\s*" + _coverage_call("optional_capabilities_view", r"&\s*extended_capabilities")
        + r"\s*,\s*" + _coverage_call("optional_profile_number_view", r"&\s*profile")
        + r"\s*,\s*" + _coverage_call("optional_profile_number_view", r"&\s*corresponding_profile")
        + r"\s*,\s*" + _coverage_call("component_style_owner_view", "main_styles")
        + r"\s*,\s*" + _coverage_call("roi_shifts_view", "main_roi_shifts")
        + r"\s*,\s*" + _coverage_call("profile_tile_inputs_view", r"tile_parts\s*@")
        + r"\s*,\s*components\s*,\s*main_has_roi_marker",
    ),
    ("src/codestream/profile.rs", "validate_part15_component_capabilities"): (
        "part1_profile_validate_components", r"\1", None,
        _coverage_call("extended_capabilities_view", "capabilities")
        + r"\s*,\s*" + _coverage_call("component_style_owner_view", "styles")
        + r"\s*,\s*" + _coverage_call("roi_shifts_view", "roi_shifts")
        + r"\s*,\s*components\s*,\s*0\s*,\s*has_roi_marker",
    ),
    ("src/codestream/profile.rs", "observe_block_coding"): (
        "part1_profile_observe", r"\1",
        r"\(\s*\*\s*final\(\s*has_legacy\s*\)\s*,\s*\*\s*final\(\s*has_ht_only\s*\)\s*,\s*\*\s*final\(\s*has_mixed\s*\)\s*\)",
        r"style\s*,\s*\(\s*\*\s*old\(\s*has_legacy\s*\)\s*,\s*\*\s*old\(\s*has_ht_only\s*\)\s*,\s*\*\s*old\(\s*has_mixed\s*\)\s*\)",
    ),
    ("src/codestream/profile.rs", "ExtendedCapabilities::advertises_part15"): (
        "part1_profile_advertises_ht", r"\1", None, _coverage_call("extended_capabilities_view", "self"),
    ),
    ("src/codestream/profile.rs", "ExtendedCapabilities::part15_allows_roi"): (
        "part1_profile_capability_flag", r"\1", None,
        _coverage_call("extended_capabilities_view", "self") + r"\s*,\s*0x1000",
    ),
    ("src/codestream/profile.rs", "ExtendedCapabilities::part15_allows_heterogeneous_headers"): (
        "part1_profile_capability_flag", r"\1", None,
        _coverage_call("extended_capabilities_view", "self") + r"\s*,\s*0x0800",
    ),
    ("src/codestream/profile.rs", "ExtendedCapabilities::part15_allows_irreversible_ht"): (
        "part1_profile_capability_flag", r"\1", None,
        _coverage_call("extended_capabilities_view", "self") + r"\s*,\s*0x0020",
    ),
}

_PROFILE_POLICY_CONTRACTS = {
    ("src/codestream/profile.rs", "ExtendedCapabilities::capability_for_part"): (
        "part2_capability_value", r"\1", None,
        _coverage_call("extended_capabilities_view", "self") + r"\s*,\s*part",
    ),
    ("src/codestream/profile.rs", "ExtendedCapabilities::part15_value"): (
        "part2_capability_value", r"\1", None,
        _coverage_call("extended_capabilities_view", "self") + r"\s*,\s*15",
    ),
    ("src/codestream/profile.rs", "ExtendedCapabilities::part15_block_mode"): (
        "part2_capability_block_mode", r"\1", None, _coverage_call("extended_capabilities_view", "self"),
    ),
    ("src/codestream/profile.rs", "ExtendedCapabilities::part15_allows_multiple_ht_sets"): (
        "part2_capability_multiple_sets", r"\1", None, _coverage_call("extended_capabilities_view", "self"),
    ),
    ("src/codestream/profile.rs", "ExtendedCapabilities::part15_magnitude_bound"): (
        "part2_capability_magnitude_bound", r"\1", None, _coverage_call("extended_capabilities_view", "self"),
    ),
    ("src/codestream/profile.rs", "CodestreamProfile::part15_allows_multiple_ht_sets"): (
        "part2_profile_multiple_sets", r"\1", None, _coverage_call("codestream_profile_capabilities", "self"),
    ),
    ("src/codestream/profile.rs", "CodestreamProfile::part15_magnitude_bound"): (
        "part2_profile_magnitude_bound", r"\1", None, _coverage_call("codestream_profile_capabilities", "self"),
    ),
    ("src/codestream/profile.rs", "CodestreamProfile::part15_requires_all_ht_blocks"): (
        "part2_profile_force_ht", r"\1", None, _coverage_call("codestream_profile_capabilities", "self"),
    ),
}

_TILE_METADATA_CONTRACTS = {
    ("src/codestream/mct.rs", "MctArray::equals"): (
        "part2_mct_array_identity", r"\1", None,
        _coverage_call("mct_array_view", "self") + r"\s*,\s*" + _coverage_call("mct_array_view", "other"),
    ),
    ("src/codestream/mct.rs", "MctCollection::equals"): (
        "part2_mct_collection_identity", r"\1", None,
        _coverage_call("mct_collection_view", "self") + r"\s*,\s*" + _coverage_call("mct_collection_view", "other"),
    ),
    ("src/codestream/mct.rs", "MctStage::equals"): (
        "part2_mct_stage_identity", r"\1", None,
        _coverage_call("mct_stage_view", "self") + r"\s*,\s*" + _coverage_call("mct_stage_view", "other"),
    ),
    ("src/codestream/mct.rs", "MultipleComponentTransform::equals"): (
        "part2_mct_identity", r"\1", None,
        _coverage_call("multiple_component_transform_view", "self") + r"\s*,\s*" + _coverage_call("multiple_component_transform_view", "other"),
    ),
    ("src/codestream/coding_style.rs", "CodingStyle::maximum_isotropic_reduction"): (
        "part2_maximum_isotropic_reduction", r"\1", None,
        _coverage_call("decomposition_selector_view", "self") + r"\s*\.0\s*,\s*"
        + _coverage_call("decomposition_selector_view", "self") + r"\s*\.1\s*,\s*0",
    ),
    ("src/decode/execution.rs", "optional_multiple_component_transforms_equal"): (
        "part2_optional_mct_identity", r"\1", None,
        _coverage_call("tile_mct_option", "left") + r"\s*,\s*" + _coverage_call("tile_mct_option", "right"),
    ),
    ("src/decode/arithmetic.rs", "wavelet_transforms_equal"): (
        "part2_decode_wavelet_agreement", r"\1", None, r"left\s*,\s*right",
    ),
    ("src/decode/execution.rs", "prepare_tile_component_resolutions"): (
        "part2_tile_component_resolutions", _coverage_call("resolution_counts_outcome_for_tile", r"\1"), None,
        r"styles\s*,\s*main\s*,\s*components\s*,\s*discard",
    ),
    ("src/decode/execution.rs", "prepare_tile_decode_metadata"): (
        "part2_tile_decode_metadata", _coverage_call("tile_decode_metadata_outcome", r"\1"), None,
        r"parts@\s*,\s*components\s*,\s*discard",
    ),
}

_LAYOUT_ACCOUNTING_CONTRACTS = {
    ("src/decode/execution.rs", "account_planned_tile"): (
        "part2_planned_tile_accounting", r"\1", None,
        _coverage_call("progression_plan_view", "plan") + r"\s*,\s*"
        + _coverage_call("crate::packet::packet_selection_view", "maximum_resolution_counts") + r"\s*,\s*initial\s*,\s*limits",
    ),
    ("src/decode/execution.rs", "count_selected_component_blocks"): (
        "part2_selected_component_blocks", r"\1", None,
        _coverage_call("prepare_plan_view", "plan") + r"\s*,\s*0\s*,\s*total",
    ),
}

_PACKET_RECONSTRUCTION_CONTRACTS = {
    ("src/decode/execution.rs", "decode_planned_tile_components"): (
        "part2_decode_planned_tile_components", _coverage_call("decoded_tile_components_outcome", r"\1"), None,
        _coverage_call("progression_plan_view", r"&\s*plan")
        + r"\s*,\s*tile_parts@\s*,\s*first\s*,\s*size\s*,\s*standard\s*,\s*"
        + _coverage_call("crate::packet::packet_selection_view", "maximum_resolution_counts")
        + r"\s*,\s*limits\s*,\s*" + _coverage_call("prepared_components_view", r"prepared@") + r"\s*,\s*mct_work",
    ),
}

_COMPONENT_TILE_PLANNING_CONTRACTS = {
    ("src/decode/planning.rs", "plan_tile_component"): (
        "part2_planned_component", _coverage_call("planned_component_outcome", r"\1"), None,
        r"size\s*,\s*coding_styles\s*,\s*quantizations\s*,\s*roi_shifts\s*,\s*component\s*,\s*selection\s*,\s*policy\s*,\s*"
        + _coverage_call("planning_precincts_view", r"precincts@") + r"\s*,\s*planned_code_blocks\s*,\s*limits",
    ),
    ("src/decode/planning.rs", "plan_progression_tile_at_selected"): (
        "part2_progression_tile_plan", _coverage_call("progression_plan_outcome", r"\1"), None,
        r"size\s*,\s*coding_style\s*,\s*coding_styles\s*,\s*quantizations\s*,\s*roi_shifts\s*,\s*"
        r"\(\s*tile_index\s*,\s*discard_levels\s*\)\s*,\s*"
        r"\(\s*allow_multiple_ht_sets\s*,\s*ht_magnitude_bound\s*,\s*force_high_throughput\s*\)\s*,\s*limits",
    ),
    ("src/decode/planning.rs", "plan_progression_tile_at_with_component_overrides"): (
        "part2_progression_tile_plan", _coverage_call("progression_plan_outcome", r"\1"), None,
        r"size\s*,\s*coding_style\s*,\s*coding_styles\s*,\s*quantizations\s*,\s*roi_shifts\s*,\s*"
        r"\(\s*tile_index\s*,\s*0\s*\)\s*,\s*\(\s*false\s*,\s*74\s*,\s*false\s*\)\s*,\s*limits",
    ),
}

_RESOLUTION_PLANNING_CONTRACTS = {
    ("src/decode/planning.rs", "prepare_resolution_plan_metadata"): (
        "part2_resolution_plan_metadata", _coverage_call("resolution_plan_metadata_outcome", r"\1"), None,
        r"size\s*,\s*style\s*,\s*component\s*,\s*selection\s*,\s*component_origin",
    ),
    ("src/decode/planning.rs", "derive_planned_precinct_origin"): (
        "part2_planned_precinct_origin", r"\1", None,
        r"first\s*,\s*across\s*,\s*precinct\s*,\s*band_size",
    ),
}

_PRECINCT_PLANNING_CONTRACTS = {
    ("src/decode/planning.rs", "plan_packet_precinct"): (
        "part2_planned_precinct", _coverage_call("planned_precinct_outcome", r"\1"), None,
        r"band\s*,\s*block_size\s*,\s*subbands@\s*,\s*range\s*,\s*style\s*,\s*policy\s*,\s*location\s*,\s*"
        r"placements@\s*,\s*planned_code_blocks\s*,\s*selected\s*,\s*limits",
    ),
}

_SUBBAND_EXECUTION_CONTRACTS = {
    ("src/decode/planning.rs", "derive_planned_subband_lattice"): (
        "part2_planned_subband_lattice", _coverage_call("planned_subband_lattice_outcome", r"\1"), None,
        r"band\s*,\s*block_size\s*,\s*subband",
    ),
    ("src/decode/planning.rs", "plan_subband_execution"): (
        "part2_planned_subband_execution", _coverage_call("planned_subband_execution_outcome", r"\1"), None,
        r"band\s*,\s*block_size\s*,\s*subband\s*,\s*style\s*,\s*policy\s*,\s*indices\s*,\s*"
        r"placements@\s*,\s*planned_code_blocks\s*,\s*selected\s*,\s*limits",
    ),
}

_CODEBLOCK_VECTOR_CONTRACTS = {
    ("src/decode/planning.rs", "append_planned_codeblock"): (
        "part2_planned_codeblock_cell", _coverage_call("planned_codeblocks_outcome", r"\1"), None,
        r"grid\s*,\s*clip\s*,\s*block\s*,\s*subband\s*,\s*style\s*,\s*policy\s*,\s*indices\s*,\s*"
        + _coverage_call("planned_codeblocks_view", r"&\s*state"),
    ),
    ("src/decode/planning.rs", "plan_codeblock_decoders"): (
        "part2_planned_codeblocks", _coverage_call("planned_codeblocks_outcome", r"\1"), None,
        r"grid\s*,\s*clip\s*,\s*blocks\s*,\s*subband\s*,\s*style\s*,\s*policy\s*,\s*indices\s*,\s*"
        r"placements@\s*,\s*planned_code_blocks\s*,\s*selected\s*,\s*limits",
    ),
}

_COMPONENT_PLAN_METADATA_CONTRACTS = {
    ("src/codestream/quantization.rs", "ComponentQuantizations::quantization"): (
        "part2_component_quantization", r"\1", None, r"self\s*,\s*component",
    ),
    ("src/codestream/quantization.rs", "RoiShifts::shift"): (
        "part2_roi_shift", r"\1", None,
        _coverage_call("roi_shifts_view", "self") + r"\s*,\s*component",
    ),
    ("src/decode/planning.rs", "prepare_component_plan_metadata"): (
        "part2_component_plan_metadata", _coverage_call("component_plan_metadata_outcome", r"\1"), None,
        r"size\s*,\s*coding_styles\s*,\s*quantizations\s*,\s*roi_shifts\s*,\s*"
        r"component\s*,\s*selection\s*,\s*force_high_throughput",
    ),
}

_PRECINCT_INITIALIZATION_CONTRACTS = {
    ("src/packet/precinct.rs", "prepare_precinct_contexts"): (
        "part2_precinct_contexts", _coverage_call("precinct_contexts_outcome", r"\1"), None,
        _coverage_call("packet_states_view", r"before_states\s*@")
        + r"\s*,\s*before_contexts\s*@\s*,\s*count\s*,\s*across\s*,\s*maximum_zero\s*,\s*tier1_style",
    ),
    ("src/packet/precinct.rs", "packet_precinct_from_subbands"): (
        "part2_precinct_from_executions", _coverage_call("packet_precinct_outcome", r"\1"), None,
        r"component\s*,\s*resolution\s*,\s*precinct\s*,\s*tier1_style\s*,\s*"
        + _coverage_call("packet_executions_view", r"before\s*@") + r"\s*,\s*limits",
    ),
}

_CODEBLOCK_PLANNING_CONTRACTS = {
    ("src/decode/planning.rs", "derive_planned_codeblock_geometry"): (
        "part2_planned_codeblock_geometry", r"\1", None, r"grid\s*,\s*clip\s*,\s*block",
    ),
    ("src/tier1/contributions.rs", "tier1_configured_decoder"): (
        "part2_tier1_configured_decoder", _coverage_call("tier1_initial_decoder_outcome", r"\1"), None,
        r"width\s*,\s*height\s*,\s*significant_bitplanes\s*,\s*orientation\s*,\s*style\s*,\s*"
        r"allow_multiple_ht_sets\s*,\s*ht_magnitude_bound",
    ),
}

_DECODER_INITIALIZATION_CONTRACTS = {
    ("src/tier1/contributions.rs", "tier1_decoder_from_dimensions"): (
        "part2_tier1_initial_decoder", _coverage_call("tier1_initial_decoder_outcome", r"\1"), None,
        r"width\s*,\s*height\s*,\s*significant_bitplanes\s*,\s*orientation\s*,\s*style",
    ),
    ("src/tier1/coding.rs", "Tier1CodingStyle::set_force_high_throughput"): (
        "part2_tier1_force_style", r"\(\s*\)", r"\*\s*" + _coverage_call("final", "self"),
        r"\*\s*" + _coverage_call("old", "self") + r"\s*,\s*required",
    ),
    ("src/tier1/contributions.rs", "Tier1CodeBlockDecoder::set_multiple_ht_sets_allowed"): (
        "part2_tier1_allow_sets", r"\(\s*\)",
        _coverage_call("tier1_decoder_state", _coverage_call("final", "self")),
        _coverage_call("tier1_decoder_state", _coverage_call("old", "self")) + r"\s*,\s*allowed",
    ),
    ("src/tier1/contributions.rs", "Tier1CodeBlockDecoder::set_ht_magnitude_bound"): (
        "part2_tier1_magnitude_bound", r"\1",
        _coverage_call("tier1_decoder_state", _coverage_call("final", "self")),
        _coverage_call("tier1_decoder_state", _coverage_call("old", "self")) + r"\s*,\s*bound",
    ),
}

_SUBBAND_VECTOR_CONTRACTS = {
    ("src/codestream/coding_style.rs", "CodingStyle::subband_count"): (
        "part2_subband_count", r"\1", None,
        _coverage_call("decomposition_selector_view", "self") + r"\s*\.0\s*,\s*"
        + _coverage_call("decomposition_selector_view", "self") + r"\s*\.1",
    ),
    ("src/decode/geometry.rs", "derive_subband_resolution"): (
        "part2_subband_resolution", _coverage_call("subbands_outcome", r"\1"), None,
        r"coding_style\s*,\s*component_bounds\s*,\s*component_depth\s*,\s*"
        + _coverage_call("codestream::quantization_view", "quantization")
        + r"\s*,\s*resolution\s*,\s*before\s*@",
    ),
    ("src/decode/geometry.rs", "derive_component_subbands_for"): (
        "part2_component_subbands", _coverage_call("subbands_outcome", r"\1"), None,
        r"size\s*,\s*coding_style\s*,\s*quantization\s*,\s*component\s*,\s*tile_index\s*,\s*roi_shift",
    ),
    ("src/decode/geometry.rs", "derive_component_subbands"): (
        "part2_component_subbands", _coverage_call("subbands_outcome", r"\1"), None,
        r"size\s*,\s*coding_style\s*,\s*quantization\s*,\s*component\s*,\s*None\s*,\s*0",
    ),
}
_SUBBAND_VECTOR_PROVED_BOUNDARY_APIS = frozenset({
    ("src/decode/geometry.rs", "derive_component_subbands"),
})

_SUBBAND_ADMISSION_CONTRACTS = {
    ("src/codestream/quantization.rs", "Quantization::step"): (
        "part2_quantization_lookup", r"\1", None,
        _coverage_call("quantization_view", "self") + r"\s*,\s*index",
    ),
    ("src/decode/geometry.rs", "quantization_step_at_index"): (
        "part2_quantization_step_at_index", r"\1", None,
        _coverage_call("codestream::quantization_view", "quantization") + r"\s*,\s*resolution\s*,\s*index",
    ),
    ("src/decode/geometry.rs", "quantization_step_for_subband"): (
        "part2_quantization_for_subband", r"\1", None,
        _coverage_call("codestream::quantization_view", "quantization") + r"\s*,\s*resolution\s*,\s*orientation",
    ),
    ("src/decode/geometry.rs", "make_subband_geometry"): (
        "part2_make_subband_geometry", r"\1", None,
        r"resolution\s*,\s*orientation\s*,\s*bounds\s*,\s*resolution_dimensions\s*,\s*"
        r"low_pass_first\s*,\s*component_depth\s*,\s*"
        + _coverage_call("codestream::quantization_view", "quantization") + r"\s*,\s*quantization_index",
    ),
}
_SUBBAND_ADMISSION_PROVED_BOUNDARY_APIS = frozenset({
    ("src/decode/geometry.rs", "quantization_step_for_subband"),
})

_PACKET_GRID_PRODUCER_CONTRACTS = {
    ("src/decode/geometry.rs", "prepare_component_resolution_counts"): (
        "part2_component_resolution_counts",
        _coverage_call("resolution_counts_outcome", r"\1"), None,
        r"components\s*,\s*coding_styles\s*,\s*discard_levels",
    ),
    ("src/decode/geometry.rs", "derive_packet_grid_for_components"): (
        "part2_packet_grid_from_components",
        _coverage_call("crate::packet::packet_grid_outcome", r"\1"), None,
        r"size\s*,\s*coding_styles\s*,\s*layers\s*,\s*limits\s*,\s*tile_index\s*,\s*discard_levels",
    ),
}


def _resolution_geometry_contracts() -> dict[tuple[str, str], tuple[str, str, str | None, str]]:
    size = r"\s*,\s*".join((
        _coverage_call("codestream::selection_geometry_view", "size"),
        _coverage_call("codestream::image_size_component_count", "size"),
        _coverage_call("codestream::image_size_component_infos", "size"),
    ))
    geometry = size + r"\s*,\s*" + _coverage_call("resolution_geometry_style", "coding_style")
    return {
        ("src/decode/geometry.rs", "derive_component_resolution_geometry"): (
            "part2_resolution_geometry", r"\1", None,
            geometry + r"\s*,\s*component\s*,\s*resolution\s*,\s*None",
        ),
        ("src/decode/geometry.rs", "derive_component_resolution_geometry_for"): (
            "part2_resolution_geometry", r"\1", None,
            geometry + r"\s*,\s*component\s*,\s*resolution\s*,\s*tile_index",
        ),
        ("src/decode/geometry.rs", "component_coordinate_bounds"): (
            "part2_component_coordinate_bounds", r"\1", None,
            size + r"\s*,\s*component\s*,\s*tile_index",
        ),
        ("src/decode/arithmetic.rs", "floor_div_u32"): (
            "part2_selection_floor", r"\1", None, r"value\s*,\s*divisor",
        ),
    }


_RESOLUTION_GEOMETRY_CONTRACTS = _resolution_geometry_contracts()
_RESOLUTION_GEOMETRY_PROVED_BOUNDARY_APIS = frozenset({
    ("src/decode/geometry.rs", "derive_component_resolution_geometry"),
})

_RESOLUTION_STYLE_CONTRACTS = {
    ("src/codestream/coding_style.rs", "CodingStyle::resolution_downsampling"): (
        "part2_resolution_downsampling", r"\1", None,
        _coverage_call("decomposition_selector_view", "self") + r"\s*\.0\s*,\s*"
        + _coverage_call("decomposition_selector_view", "self") + r"\s*\.1\s*,\s*resolution",
    ),
    ("src/codestream/coding_style.rs", "CodingStyle::resolution_downsampling_step"): (
        "part2_resolution_scale_step", r"\1", None,
        _coverage_call("decomposition_selector_view", "self") + r"\s*\.0\s*,\s*"
        + _coverage_call("decomposition_selector_view", "self") + r"\s*\.1\s*,\s*stage\s*,\s*scales",
    ),
    ("src/codestream/coding_style.rs", "CodingStyle::precinct_exponents"): (
        "part2_precinct_exponents", r"\1", None,
        _coverage_call("precinct_selector_view", "self") + r"\s*\.0\s*,\s*"
        + _coverage_call("precinct_selector_view", "self") + r"\s*\.1\s*,\s*resolution",
    ),
}

_TILE_COMPONENT_GEOMETRY_CONTRACTS = {
    ("src/codestream/geometry.rs", "registered_ceil_div"): (
        "part2_registered_component_ceil", r"\1", None,
        r"value\s*,\s*divisor\s*,\s*registration",
    ),
    ("src/decode/arithmetic.rs", "registered_ceil_div_u32"): (
        "part2_registered_decode_ceil", r"\1", None,
        r"value\s*,\s*divisor\s*,\s*registration",
    ),
    ("src/codestream/geometry.rs", "ImageSize::tile_component_bounds"): (
        "part2_tile_component_bounds", r"\1", None,
        r"\s*,\s*".join((
            _coverage_call("selection_geometry_view", "self"),
            _coverage_call("image_size_component_count", "self"),
            _coverage_call("image_size_component_infos", "self"),
            "tile_index", "component",
        )),
    ),
}

_LAYER_REGISTRATION_CONTRACTS = {
    ("src/jpx/resources.rs", "registered_extent"): (
        "part2_native_registered_extent", r"\1", None,
        r"samples\s*,\s*subsampling\s*,\s*grid_size\s*,\s*offset",
    ),
    ("src/jpx/registration.rs", "registered_layer_geometry"): (
        "part2_registered_layer_geometry", r"\1", None,
        r"source_width\s*,\s*source_height\s*,\s*"
        + _coverage_call("layer_registration_view", "registration")
        + r"\s*,\s*horizontal_grid_size\s*,\s*vertical_grid_size",
    ),
}

_LAYER_SAMPLING_CONTRACTS = {
    ("src/jpx/registration.rs", "copy_registered_color"): (
        "part2_registered_color_store", r"\1",
        _coverage_call("crate::specs::part2_composition_planes", _coverage_call("final", "colors") + r"\s*@"),
        r"\s*,\s*".join((
            _coverage_call("crate::specs::part2_composition_planes", _coverage_call("old", "colors") + r"\s*@"),
            _coverage_call("owned_layer_view", "source") + r"\s*\.3",
            r"color\s+as\s+nat", "source_index", "destination",
        )),
    ),
    ("src/jpx/registration.rs", "copy_registered_pixel"): (
        "part2_registered_pixel", r"\1",
        _coverage_call("crate::specs::part2_composition_planes", _coverage_call("final", "colors") + r"\s*@")
        + r"\s*,\s*" + _coverage_call("final", "alpha") + r"\s*@",
        r"\s*,\s*".join((
            _coverage_call("owned_layer_view", "source"),
            _coverage_call("crate::specs::part2_composition_planes", _coverage_call("old", "colors") + r"\s*@"),
            _coverage_call("old", "alpha") + r"\s*@",
            r"source_position\.0", r"source_position\.1",
            r"destination_position\.0", r"destination_position\.1", r"destination_position\.2",
        )),
    ),
}

_LAYER_TRAVERSAL_CONTRACTS = {
    ("src/jpx/registration.rs", "register_layer"): (
        "part2_register_layer", _coverage_call("owned_layer_outcome", r"\1"), None,
        r"\s*,\s*".join((
            _coverage_call("owned_layer_view", "source"),
            _coverage_call("layer_registration_view", "registration"),
            "horizontal_grid_size", "vertical_grid_size",
        )),
    ),
    ("src/jpx/registration.rs", "copy_registered_row"): (
        "part2_registered_row", r"\1",
        _coverage_call("crate::specs::part2_composition_planes", _coverage_call("final", "colors") + r"\s*@")
        + r"\s*,\s*" + _coverage_call("final", "alpha") + r"\s*@",
        r"\(\s*" + r"\s*,\s*".join((
            _coverage_call("owned_layer_view", "source"),
            _coverage_call("layer_registration_view", "registration"),
            "grids", r"destination\.0",
        )) + r"\s*\)\s*,\s*destination\.1\s*,\s*"
        + _coverage_call("crate::specs::part2_composition_planes", _coverage_call("old", "colors") + r"\s*@")
        + r"\s*,\s*" + _coverage_call("old", "alpha") + r"\s*@",
    ),
}

_LAYER_KEY_CONTRACTS = {
    ("src/jpx/chroma.rs", "normalized_chroma_keys"): (
        "part2_normalized_chroma_keys", _coverage_call("crate::color::normalized_plane_result", r"\1"), None,
        r"values\s*@\s*,\s*channels\s*,\s*bit_depth",
    ),
}

_LAYER_COMPONENT_KEY_CONTRACTS = {
    ("src/jpx/chroma.rs", "normalized_chroma_keys_for_components"): (
        "part2_normalized_component_chroma_keys", _coverage_call("crate::color::normalized_plane_result", r"\1"), None,
        r"values\s*@\s*,\s*descriptors\s*@",
    ),
    ("src/jpx/chroma.rs", "append_component_chroma_key"): (
        "part2_append_component_key", r"\1",
        _coverage_call("final", "keys") + r"\s*@\s*,\s*\*\s*" + _coverage_call("final", "offset"),
        r"values\s*@\s*,\s*descriptor\s*,\s*"
        + _coverage_call("old", "keys") + r"\s*@\s*,\s*\*\s*" + _coverage_call("old", "offset"),
    ),
}

_LAYER_OPACITY_CONTRACTS = {
    ("src/jpx/chroma.rs", "apply_chroma_key_with_policy"): (
        "part2_apply_chroma_key_policy", r"\1",
        _coverage_call("owned_layer_view", _coverage_call("final", "owned")),
        _coverage_call("owned_layer_view", _coverage_call("old", "owned")) + r"\s*,\s*keys\s*@\s*,\s*reject_missing",
    ),
    ("src/jpx/opacity.rs", "set_layer_alpha_mode"): (
        "part2_set_layer_alpha_mode", r"\1",
        _coverage_call("owned_layer_view", _coverage_call("final", "owned")),
        _coverage_call("owned_layer_view", _coverage_call("old", "owned")) + r"\s*,\s*premultiplied\s*,\s*offset",
    ),
}

_LAYER_EXTERNAL_ALPHA_CONTRACTS = {
    ("src/jpx/opacity.rs", "copy_registered_layer_opacity"): (
        "part2_copy_registered_opacity", r"\1",
        _coverage_call("owned_layer_view", _coverage_call("final", "owned")),
        _coverage_call("owned_layer_view", _coverage_call("old", "owned")) + r"\s*,\s*"
        + _coverage_call("owned_layer_view", "source") + r"\s*,\s*premultiplied",
    ),
    ("src/jpx/opacity.rs", "copy_opacity_pixel"): (
        "part2_opacity_pixel", r"\1", _coverage_call("final", "alpha") + r"\s*@",
        r"\(\s*samples\s*@\s*,\s*geometry\.0\s*,\s*geometry\.1\s*\)\s*,\s*"
        r"geometry\.2\s*,\s*geometry\.3\s*,\s*" + _coverage_call("old", "alpha") + r"\s*@",
    ),
    ("src/jpx/opacity.rs", "copy_opacity_row"): (
        "part2_opacity_columns_prefix", r"\1", _coverage_call("final", "alpha") + r"\s*@",
        r"\(\s*samples\s*@\s*,\s*source_width\s*,\s*destination\.0\s*\)\s*,\s*"
        r"destination\.1\s*,\s*" + _coverage_call("old", "alpha") + r"\s*@\s*,\s*destination\.2\s+as\s+nat",
    ),
}


_DECODER_ADMISSION_CONTRACTS = {
    ("src/decode/execution.rs", "validate_part2_coding_style"): (
        "part2_validate_execution_style", r"\1", None,
        r"style\s*,\s*" + _coverage_call("codestream::part2_execution_registry", "extensions")
        + r"\s*,\s*" + _coverage_call("codestream::part2_kernel_registry", "extensions"),
    ),
    ("src/codestream/extensions.rs", "Part2Extensions::component_bit_depths_equal"): (
        "part2_component_depths_equal", r"\1", None,
        _coverage_call("part2_component_depths", "self") + r"\s*,\s*" + _coverage_call("part2_component_depths", "other"),
    ),
}

_DECODER_LAYOUT_CONTRACTS = {
    ("src/decode/execution.rs", "validate_part2_component"): (
        "part2_validate_execution_component", r"\1", None,
        _coverage_call("execution_header_view", r"\*\s*styles", "extensions") + r"\s*,\s*component",
    ),
    ("src/decode/execution.rs", "validate_part2_components"): (
        "part2_execution_components_prefix", r"\1", None,
        _coverage_call("execution_header_view", r"\*\s*styles", "extensions") + r"\s*,\s*count\s+as\s+nat",
    ),
    ("src/decode/execution.rs", "validate_part2_tile_execution"): (
        "part2_validate_execution_tile", r"\1", None,
        _coverage_call("execution_header_view", r"part\.component_coding_styles", r"&\s*part\.part2_extensions")
        + r"\s*,\s*" + _coverage_call("codestream::part2_component_depths", "main") + r"\s*,\s*count",
    ),
    ("src/decode/execution.rs", "validate_part2_execution"): (
        "part2_validate_execution_layout", r"\1", None,
        r"layout\.info\.image_size\.components\s*,\s*"
        + _coverage_call("execution_header_view", r"layout\.info\.component_coding_styles", r"&\s*layout\.info\.part2_extensions")
        + r"\s*,\s*" + _coverage_call("execution_tile_headers", r"layout\.tile_parts\s*@"),
    ),
}


_SOURCE_OPACITY_ENTRY = "part2-complete-native-source-layer-opacity-result"
_RAW_COMPOSITION_ENTRY = "part2-complete-native-raw-composition-and-reference-results"
_RAW_COMPOSITION_CONTRACTS = {
    ("src/jp2/composition.rs", "has_explicit_registration"): (
        "part2_any_layer_registration", r"\1", None,
        _coverage_call("super::raw_compositing_layers_view", r"layers\s*@") + r"\s*,\s*layers\.len\(\)\s+as\s+nat",
    ),
    ("src/jp2/composition.rs", "parse_instruction_set"): (
        "part2_parse_instruction_set", _coverage_call("super::raw_instruction_set_outcome", r"\1"), None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*composition\s*,\s*base_offset\s*,\s*limits",
    ),
    ("src/jp2/composition.rs", "read_u32_at"): (
        "part2_read_composition_word", r"\1", r"\*\s*" + _coverage_call("final", "position"),
        r"input\s*@\s*,\s*\*\s*" + _coverage_call("old", "position") + r"\s*,\s*offset",
    ),
    ("src/jp2/composition.rs", "validate_dimensions"): (
        "part2_validate_composition_dimensions", r"\1", None, r"width\s*,\s*height\s*,\s*limits\s*,\s*offset",
    ),
    ("src/jp2/composition.rs", "parse_composition"): (
        "part2_parse_composition", _coverage_call("super::raw_composition_outcome", r"\1"), None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*\*\s*limits",
    ),
    ("src/jp2/composition.rs", "validate_layer_references"): (
        "part2_validate_layer_references", r"\1", None,
        _coverage_call("super::raw_compositing_layers_view", r"layers\s*@") + r"\s*,\s*codestream_count",
    ),
}
_RAW_COMPOSITION_MODELS = {
    ("specs/jp2_composition.rs", name) for name in (
        "part2_parse_instruction_set", "part2_instruction_record", "part2_instruction_records",
        "part2_instruction_result", "part2_instruction_record_words", "part2_read_composition_word",
        "part2_validate_composition_dimensions", "part2_parse_composition", "part2_composition_boxes", "part2_composition_finish",
    )
} | {
    ("specs/jp2_layer.rs", name) for name in ("part2_validate_layer_references", "part2_layer_references", "part2_layer_registration_references", "part2_any_layer_registration")
}
_RAW_COMPOSITION_PROOFS = {
    ("src/jp2/composition.rs", "has_explicit_registration"),
} | {
    ("src/jp2/proof_support.rs", name) for name in (
        "raw_instruction_set_view", "raw_instruction_set_outcome", "raw_instruction_sets_view",
        "raw_composition_view", "raw_composition_outcome", "raw_compositing_layers_view",
    )
}
_RAW_LAYER_HEADER_ENTRY = "part2-complete-native-raw-compositing-layer-result"
_RAW_LAYER_HEADER_CONTRACTS = {
    ("src/jp2/composition.rs", "parse_codestream_registration"): (
        "part2_parse_codestream_registration", _coverage_call("super::registration_outcome", r"\1"), None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*base_offset\s*,\s*limits",
    ),
    ("src/jp2/composition.rs", "parse_color_group"): (
        "part2_parse_color_group", _coverage_call("super::color_group_outcome", r"\1"), None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*\*\s*limits\s*,\s*base_offset",
    ),
    ("src/jp2/composition.rs", "parse_layer_opacity"): (
        "part2_parse_layer_opacity", _coverage_call("super::opacity_outcome", r"\1"), None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*base_offset",
    ),
    ("src/jp2/composition.rs", "parse_compositing_layer"): (
        "part2_parse_compositing_layer", _coverage_call("super::raw_compositing_layer_outcome", r"\1"), None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*\*\s*limits",
    ),
}
_RAW_LAYER_HEADER_MODELS = {
    ("specs/jp2_layer.rs", name) for name in (
        "part2_parse_codestream_registration", "part2_registration_entry", "part2_registration_prefix",
        "part2_parse_layer_opacity", "part2_parse_color_group", "part2_color_group_boxes",
        "part2_color_group_finish", "part2_parse_compositing_layer", "part2_raw_layer_boxes", "part2_raw_layer_step",
    )
} | {("src/limits.rs", "resource_codestream_limit")}
_RAW_LAYER_HEADER_PROOFS = {
    ("src/jp2/proof_support.rs", name) for name in (
        "registration_outcome", "full_color_group_view", "color_group_outcome", "opacity_outcome",
        "raw_compositing_layer_view", "raw_compositing_layer_outcome", "raw_compositing_layer_state", "raw_compositing_layer_payload_reference",
    )
} | {
    ("specs/jp2_layer.rs", name) for name in ("part2_registration_step", "part2_registration_error")
} | {("src/limits.rs", "ResourceLimits::maximum_codestreams")}
_METADATA_TREE_ENTRY = "part2-complete-native-raw-metadata-tree-result"
_METADATA_TREE_CONTRACTS = {
    ("src/jp2/metadata.rs", "inspect_metadata_box"): (
        "part2_inspect_metadata_box", r"\1", None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*\*\s*limits\s*,\s*depth\s*,\s*remaining_depth",
    ),
}
_METADATA_TREE_MODELS = {
    ("specs/jp2_metadata.rs", "part2_inspect_metadata_box"),
    ("specs/jp2_metadata.rs", "part2_metadata_children"),
    ("specs/mod.rs", "part2_metadata_count"),
    ("src/limits.rs", "resource_box_depth_limit"),
}
_METADATA_TREE_PROOFS = {
    ("specs/jp2_metadata.rs", "part2_metadata_start"),
    ("src/limits.rs", "resource_box_depth_limit"),
    ("src/limits.rs", "ResourceLimits::maximum_box_depth"),
    ("src/refinement/headers.rs", "metadata_count"),
}
_OWNED_HEADER_CLONE_ENTRY = "part2-complete-native-owned-header-clone-producers"
_ASSOCIATION_CLONE_ENTRY = "part2-complete-native-owned-codestream-association-clone-producers"
_RAW_CONTAINER_ENTRY = "part2-complete-native-raw-container-result"
_RAW_INSPECTED_ENTRY = "part2-complete-native-raw-inspected-container-results"
_RAW_INSPECTED_CONTRACTS = {
    ("src/jp2/container.rs", "parse_and_inspect"): (
        "part2_parse_and_inspect_container", _coverage_call("super::raw_inspected_container_outcome", r"\1"), None,
        r"input\s*@\s*,\s*limits",
    ),
    ("src/jp2/container.rs", "parse_and_inspect_for_display"): (
        "part2_parse_and_inspect_container_mode", _coverage_call("super::raw_inspected_container_outcome", r"\1"), None,
        r"input\s*@\s*,\s*limits\s*,\s*true",
    ),
    ("src/jp2/container.rs", "parse_and_inspect_mode"): (
        "part2_parse_and_inspect_container_mode", _coverage_call("super::raw_inspected_container_outcome", r"\1"), None,
        r"input\s*@\s*,\s*limits\s*,\s*display_first",
    ),
    ("src/jp2/container.rs", "inspection_count"): (
        "part2_inspection_count", r"\1\s+as\s+nat", None,
        _coverage_call("super::raw_jp2_file_view", "file") + r"\s*,\s*display_first",
    ),
    ("src/jp2/container.rs", "inspect_jph"): (
        "part2_inspect_jph_container", _coverage_call("super::raw_inspected_container_outcome", r"\1"), None,
        r"input\s*@\s*,\s*limits",
    ),
    ("src/codestream/profile.rs", "CodestreamProfile::is_part15"): (
        "part1_profile_optional_advertises_ht", r"\1", None,
        _coverage_call("codestream_profile_capabilities", "self"),
    ),
}
_RAW_INSPECTED_MODELS = {
    ("specs/jp2_inspection.rs", name) for name in (
        "part2_parse_and_inspect_container", "part2_inspect_jph_container",
        "part2_parse_and_inspect_container_mode", "part2_inspection_count",
        "part2_inspected_codestreams", "part2_inspected_header",
    )
} | {
    ("specs/jp2_container.rs", "part2_parse_container"),
    ("specs/raw_layout.rs", "part1_parse_info"),
    ("specs/codestream_profile.rs", "part1_profile_optional_advertises_ht"),
}
_RAW_INSPECTED_PROOFS = {
    ("src/jp2/proof_support.rs", name) for name in (
        "raw_inspected_container_outcome", "raw_inspected_container_view", "raw_codestream_infos_view",
        "raw_inspection_file_fields_known", "raw_association_reference_option",
        "raw_jp2_file_view", "raw_codestream_view", "raw_codestream_association_view",
    )
} | {
    ("specs/jp2_inspection.rs", "part2_parse_and_inspect_container_unfold"),
    ("specs/jp2_inspection.rs", "part2_parse_and_inspect_container_mode_unfold"),
    ("specs/jp2_inspection.rs", "part2_inspect_jph_container_unfold"),
    ("src/codestream/proof_support.rs", "complete_codestream_info_view"),
    ("src/codestream/proof_support.rs", "complete_codestream_info_known_fields"),
    ("src/jp2/container.rs", "Jp2File::codestream_count"),
    ("src/jp2/container.rs", "Jp2File::codestream"),
    ("src/jp2/container.rs", "CodestreamBox::codestream_header"),
}
_RAW_CONTAINER_CONTRACTS = {
    ("src/jp2/container.rs", "parse"): (
        "part2_parse_container", _coverage_call("super::raw_jp2_file_outcome", r"\1"), None,
        r"input\s*@\s*,\s*\*\s*limits",
    ),
}
_RAW_CONTAINER_MODELS = {
    ("specs/jp2_container.rs", name) for name in (
        "part2_parse_container", "part2_container_boxes", "part2_container_step",
        "part2_container_finish", "part2_container_attach", "part2_container_initial_state",
        "part2_container_next_stream_count", "part2_container_error",
    )
} | {
    ("specs/jp2_file_type.rs", "part2_container_prologue"),
    ("specs/jp2_header.rs", "part2_parse_jp2_header_profile"),
}
_RAW_CONTAINER_PROOFS = {
    ("src/jp2/proof_support.rs", name) for name in (
        "raw_jp2_file_outcome", "raw_jp2_file_view", "raw_container_state",
        "raw_codestream_view", "raw_codestreams_view", "raw_codestream_associations_view",
        "raw_codestream_association_view", "raw_jp2_header_view", "raw_composition_option",
        "raw_compositing_layers_view",
    )
}
_ASSOCIATION_CLONE_CONTRACTS = {
    ("src/jp2/clone_support.rs", "optional_jp2_header_clone"): (
        "part2_optional_jp2_header_clone", _coverage_call("super::optional_jp2_header_view", r"&\s*\1"), None,
        _coverage_call("super::optional_jp2_header_view", "source"),
    ),
    ("src/jp2/clone_support.rs", "codestream_association_clone"): (
        "part2_codestream_association_clone", _coverage_call("super::raw_codestream_association_view", r"&\s*\1"), None,
        _coverage_call("super::raw_codestream_association_view", "source"),
    ),
}
_ASSOCIATION_CLONE_MODELS = {
    ("specs/jp2_associated_header.rs", name) for name in ("part2_optional_jp2_header_clone", "part2_codestream_association_clone")
}
_ASSOCIATION_CLONE_PROOFS = {
    ("src/jp2/proof_support.rs", name) for name in (
        "optional_jp2_header_view", "raw_jp2_header_view", "raw_codestream_association_view", "raw_codestream_association_payload_reference",
    )
}
_OWNED_HEADER_CLONE_CONTRACTS = {
    ("src/jp2/clone_support.rs", "color_specification_clone"): (
        "part2_color_specification_clone", _coverage_call("super::full_color_specification_view", r"&\s*\1"), None,
        _coverage_call("super::full_color_specification_view", "source"),
    ),
    ("src/jp2/clone_support.rs", "palette_clone"): (
        "part2_owned_palette_clone", _coverage_call("super::palette_view", r"&\s*\1"), None,
        _coverage_call("super::palette_view", "source"),
    ),
    ("src/jp2/clone_support.rs", "optional_palette_clone"): (
        "part2_optional_palette_clone", _coverage_call("super::optional_palette_view", r"&\s*\1"), None,
        _coverage_call("super::optional_palette_view", "source"),
    ),
    ("src/jp2/clone_support.rs", "jp2_header_clone"): (
        "part2_jp2_header_clone", _coverage_call("super::raw_jp2_header_view", r"&\s*\1"), None,
        _coverage_call("super::raw_jp2_header_view", "source"),
    ),
}
_OWNED_HEADER_CLONE_MODELS = {
    ("specs/jp2_associated_header.rs", name) for name in (
        "part2_color_specification_clone", "part2_owned_palette_clone", "part2_optional_palette_clone", "part2_jp2_header_clone",
    )
}
_OWNED_HEADER_CLONE_PROOFS = {
    ("src/jp2/proof_support.rs", name) for name in (
        "full_color_specification_view", "palette_view", "optional_palette_view", "raw_jp2_header_view",
    )
}
_ASSOCIATED_HEADER_ENTRY = "part2-complete-native-associated-codestream-header-result"
_ASSOCIATED_HEADER_CONTRACTS = {
    ("src/jp2/headers.rs", "parse_codestream_header"): (
        "part2_parse_codestream_header", _coverage_call("super::raw_jp2_header_outcome", r"\1"), None,
        r"payload\s*@\s*,\s*" + _coverage_call("super::raw_header_option", "defaults") + r"\s*,\s*\*\s*limits\s*,\s*base_offset",
    ),
}
_ASSOCIATED_HEADER_MODELS = {
    ("specs/jp2_associated_header.rs", name) for name in (
        "part2_parse_codestream_header", "part2_associated_header_boxes", "part2_associated_header_step",
        "part2_associated_header_finish", "part2_jp2_header_clone",
    )
} | {
    ("specs/jp2_header.rs", "part2_parse_jp2_header"),
    ("specs/jp2_color_header.rs", "part2_validate_color_specification_prefix"),
}
_ASSOCIATED_HEADER_PROOFS = {
    ("src/jp2/proof_support.rs", name) for name in ("raw_header_option", "associated_header_state", "raw_jp2_header_outcome")
} | {("src/jp2/clone_support.rs", "jp2_header_clone")}
_RAW_JP2_HEADER_ENTRY = "part2-complete-native-raw-jp2-header-result"
_RAW_JP2_HEADER_CONTRACTS = {
    ("src/jp2/headers.rs", "parse_jp2_header"): (
        "part2_parse_jp2_header", _coverage_call("super::raw_jp2_header_outcome", r"\1"), None,
        r"payload\s*@\s*,\s*\*\s*limits\s*,\s*base_offset",
    ),
    ("src/jp2/headers.rs", "parse_jp2_header_profile"): (
        "part2_parse_jp2_header_profile", _coverage_call("super::raw_jp2_header_outcome", r"\1"), None,
        r"payload\s*@\s*,\s*\*\s*limits\s*,\s*base_offset\s*,\s*allow_unspecified",
    ),
    ("src/jp2/headers.rs", "unspecified_jph_color"): (
        "part2_unspecified_jph_color", _coverage_call("super::color_specification_outcome", r"\1"), None,
        _coverage_call("super::channel_definition_records_view", r"definitions\s*@") + r"\s*,\s*base_offset",
    ),
}
_RAW_JP2_HEADER_MODELS = {
    ("specs/jp2_header.rs", name) for name in (
        "part2_parse_jp2_header", "part2_parse_jp2_header_profile", "part2_unspecified_jph_color",
        "part2_raw_header_boxes", "part2_raw_header_step",
        "part2_raw_header_finish", "part2_raw_header_missing",
    )
} | {
    ("specs/jp2_box_reader.rs", name) for name in ("part2_box_reader_from_input", "part2_box_reader_required")
} | {
    ("specs/jp2_image_header.rs", name) for name in ("part2_parse_image_header", "part2_validate_bpcc")
} | {
    ("specs/jp2_color_header.rs", "part2_parse_color_specification"),
    ("specs/jp2_color_header.rs", "part2_validate_color_specification_prefix"),
    ("specs/jp2_palette.rs", "part2_parse_palette"),
    ("specs/jp2_channel_header.rs", "part2_parse_component_mapping"),
    ("specs/jp2_channel_header.rs", "part2_parse_channel_definition"),
    ("specs/jp2_resolution.rs", "part2_parse_resolution_superbox"),
}
_RAW_JP2_HEADER_PROOFS = {
    ("src/jp2/proof_support.rs", name) for name in (
        "raw_header_state", "raw_jp2_header_view", "raw_jp2_header_outcome",
        "full_color_specification_view", "color_specification_outcome", "channel_definition_records_view",
    )
}
_RAW_JP2_HEADER_TESTS = {
    ("src/jp2/tests.rs", name) for name in (
        "actual_raw_jp2_header_retains_every_owned_metadata_field_from_real_raw_producers",
        "actual_raw_jp2_header_preserves_first_color_and_ignores_later_interpretations",
        "actual_raw_jp2_header_keeps_initial_required_input_metadata_and_later_progress_priority",
        "actual_raw_jp2_header_keeps_duplicate_checks_and_resolution_parse_before_duplicate",
        "actual_raw_jp2_header_keeps_final_bpcc_palette_mapping_and_color_requirements",
        "actual_raw_jp2_header_uses_actual_mapping_count_at_the_channel_definition_site",
        "sarah_dev_629a0a9c39_later_colour_interpretations_preserve_selected_metadata",
        "sarah_dev_629a0a9c39_ignored_prefixes_keep_selected_and_error_policies",
    )
} | {
    ("src/jp2/tests.rs", "sarah_dev_174ec5fee4_only_declared_jph_profile_admits_absent_colour"),
    ("src/jp2/tests.rs", "sarah_dev_174ec5fee4_unspecified_jph_rejects_colour_channel_claims"),
    ("src/decode/tests.rs", "sarah_dev_174ec5fee4_jph_components_do_not_require_specified_colour"),
}
_PALETTE_RESULT_ENTRY = "part2-complete-native-raw-owned-palette-result"
_PALETTE_RESULT_CONTRACTS = {
    ("src/jp2/color.rs", "parse_palette"): (
        "part2_parse_palette", _coverage_call("super::palette_outcome", r"\1"), None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*base_offset",
    ),
}
_PALETTE_RESULT_MODELS = {
    ("specs/jp2_palette.rs", name) for name in (
        "part2_parse_palette", "part2_palette_descriptors", "part2_palette_descriptor_step",
        "part2_palette_value_step", "part2_palette_row", "part2_palette_rows", "part2_parse_palette_value",
    )
} | {("specs/jp2_image_header.rs", "part2_container_bit_depth")}
_PALETTE_RESULT_PROOFS = {
    ("specs/jp2_palette.rs", name) for name in (
        "part2_palette_descriptors_step", "part2_palette_descriptors_error",
        "part2_palette_row_step", "part2_palette_row_error", "part2_palette_rows_step", "part2_palette_rows_error",
    )
} | {("src/jp2/proof_support.rs", name) for name in ("palette_outcome", "palette_view")} \
    | {("src/jp2/color.rs", "parse_palette_value"), ("src/jp2/headers.rs", "parse_bit_depth")}
_PALETTE_RESULT_TESTS = {("src/jp2/tests.rs", name) for name in (
    "actual_raw_palette_result_keeps_every_descriptor_byte_and_complete_owned_fields",
    "actual_raw_palette_result_keeps_dimension_descriptor_then_sample_error_priority",
    "actual_raw_palette_result_retains_ordered_mixed_width_rows_and_source_independent_owners",
    "actual_raw_palette_result_bounds_entries_and_preserves_full_column_count",
    "sarah_dev_2032f100c3_palette_entry_domain_and_error_priority",
    "sarah_dev_2032f100c3_palette_domain_reaches_full_and_associated_headers",
)}
_PALETTE_VALUE_ENTRY = "part2-complete-native-raw-palette-scalar-result"
_PALETTE_VALUE_CONTRACTS = {
    ("src/jp2/color.rs", "parse_palette_value"): (
        "part2_parse_palette_value", r"\1", None, r"bytes\s*@\s*,\s*precision\s*,\s*signed\s*,\s*offset",
    ),
}
_PALETTE_VALUE_MODELS = {
    ("specs/jp2_palette.rs", name) for name in (
        "part2_parse_palette_value", "part2_palette_word_prefix",
        "part2_palette_modulus_prefix", "part2_palette_arithmetic_error",
    )
}
_PALETTE_VALUE_PROOFS = {
    ("specs/jp2_palette.rs", name) for name in (
        "part2_palette_word_step", "part2_palette_word_error",
        "part2_palette_modulus_step", "part2_palette_modulus_error",
    )
}
_RESOLUTION_ENTRY = "part2-complete-native-raw-resolution-and-metadata-copy-results"
_RESOLUTION_CONTRACTS = {
    ("src/jp2/metadata.rs", "parse_resolution"): (
        "part2_parse_resolution", r"\1", None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*base_offset",
    ),
    ("src/jp2/metadata.rs", "parse_resolution_superbox"): (
        "part2_parse_resolution_superbox", r"\1", None, r"payload\s*@\s*,\s*\*\s*limits\s*,\s*base_offset",
    ),
    ("src/jp2/metadata.rs", "copy_bytes"): (
        "part2_copy_metadata_bytes", _coverage_call("super::metadata_bytes_outcome", r"\1"), None, r"input\s*@",
    ),
}
_RESOLUTION_MODELS = {
    ("specs/jp2_resolution.rs", name) for name in (
        "part2_parse_resolution", "part2_parse_resolution_superbox", "part2_resolution_boxes",
        "part2_resolution_finish", "part2_resolution_progress_error", "part2_copy_metadata_bytes",
    )
}
_RESOLUTION_PROOFS = {
    ("src/jp2/proof_support.rs", "metadata_bytes_outcome"),
    ("src/jp2/box_reader.rs", "box_reader_from_input"),
}
_CHANNEL_HEADER_ENTRY = "part2-complete-native-raw-component-and-channel-header-results"
_CHANNEL_HEADER_CONTRACTS = {
    ("src/jp2/color.rs", "parse_component_mapping"): (
        "part2_parse_component_mapping", _coverage_call("super::component_mapping_outcome", r"\1"), None,
        _coverage_call("super::box_reference_view", "box_ref")
        + r"\s*,\s*components\s*,\s*palette_columns\s*,\s*limits\s*,\s*base_offset",
    ),
    ("src/jp2/color.rs", "parse_channel_definition"): (
        "part2_parse_channel_definition", _coverage_call("super::channel_definition_records_outcome", r"\1"), None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*output_channels\s*,\s*base_offset",
    ),
}
_CHANNEL_HEADER_MODELS = {
    ("specs/jp2_channel_header.rs", name) for name in (
        "part2_parse_component_mapping", "part2_mapping_entry", "part2_parse_channel_definition", "part2_channel_record",
    )
} | {("specs/mod.rs", name) for name in ("part2_component_mapping_valid", "part2_channel_definition_valid")}
_CHANNEL_HEADER_PROOFS = {
    ("src/jp2/proof_support.rs", name) for name in (
        "component_mapping_outcome", "channel_definition_records_view", "channel_definition_records_outcome",
    )
} | {
    ("specs/jp2_channel_header.rs", name) for name in (
        "part2_mapping_step", "part2_mapping_error", "part2_channel_records_step", "part2_channel_records_error",
    )
} | {
    ("src/image/layout.rs", "channel_definition_new"),
    ("proofs/spec_properties/mod.rs", "channel_definition_admission_is_independent_of_association"),
}
_COLOR_HEADER_ENTRY = "part2-complete-native-raw-color-header-result"
_COLOR_HEADER_CONTRACTS = {
    ("src/jp2/color.rs", "validate_color_specification_prefix"): (
        "part2_validate_color_specification_prefix", r"\1", None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*base_offset",
    ),
    ("src/jp2/color.rs", "parse_color_specification"): (
        "part2_parse_color_specification", _coverage_call("super::color_specification_outcome", r"\1"), None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*base_offset",
    ),
}
_COLOR_HEADER_PROOFS = {
    ("src/jp2/proof_support.rs", name) for name in (
        "full_color_specification_view", "color_specification_outcome", "optional_profile_bytes",
    )
} | {("src/jp2/color.rs", "copy_profile")}
_IMAGE_HEADER_ENTRY = "part2-complete-native-raw-image-header-result"
_IMAGE_HEADER_CONTRACTS = {
    ("src/jp2/headers.rs", "parse_image_header"): (
        "part2_parse_image_header", r"\1", None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*limits\s*,\s*base_offset",
    ),
    ("src/jp2/headers.rs", "parse_bit_depth"): (
        "part2_container_bit_depth", r"\1", None, r"value\s*,\s*offset",
    ),
    ("src/jp2/headers.rs", "validate_bpcc"): (
        "part2_validate_bpcc", r"\1", None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*image\s*,\s*base_offset",
    ),
}
_IMAGE_HEADER_MODELS = {("specs/jp2_image_header.rs", name) for name in (
    "part2_parse_image_header", "part2_container_bit_depth", "part2_validate_bpcc",
    "part2_bpcc_prefix", "part2_image_box_error",
)}
_IMAGE_HEADER_PROOFS = {("specs/jp2_image_header.rs", name) for name in ("part2_bpcc_step", "part2_bpcc_error")}
_FILE_TYPE_ENTRY = "part2-complete-native-raw-file-type-result"
_FILE_TYPE_CONTRACTS = {
    ("src/jp2/container.rs", "parse_file_type"): (
        "part2_parse_file_type", _coverage_call("super::file_type_outcome", r"\1"), None,
        _coverage_call("super::box_reference_view", "box_ref") + r"\s*,\s*"
        + _coverage_call("crate::limits::resource_compatible_brand_limit", "limits"),
    ),
    ("src/jp2/container.rs", "validate_file_type_profile"): (
        "part2_validate_file_type_profile", r"\1", None,
        _coverage_call("super::file_type_view", "file_type") + r"\s*,\s*offset",
    ),
}
_FILE_TYPE_MODELS = {("specs/jp2_file_type.rs", name) for name in (
    "part2_parse_file_type", "part2_file_type_brand_at", "part2_file_type_brands_prefix",
    "part2_validate_file_type_profile", "part2_container_prologue",
)}
_FILE_TYPE_PROOFS = {("specs/jp2_file_type.rs", name) for name in (
    "part2_file_type_brands_step", "part2_file_type_brands_error",
)} | {("src/jp2/proof_support.rs", name) for name in (
    "file_type_view", "file_type_outcome", "container_prefix_relation",
)}
_BOX_READER_ENTRY = "part2-complete-native-raw-box-reader-result"
_BOX_READER_CONTRACTS = {
    ("src/jp2/box_reader.rs", "BoxReader::next_box_ref"): (
        "part2_box_reader_next_ref", _coverage_call("super::box_ref_outcome", r"\1"),
        _coverage_call("super::box_reader_state", _coverage_call("final", "self")),
        _coverage_call("super::box_reader_state", _coverage_call("old", "self")),
    ),
    ("src/jp2/box_reader.rs", "BoxReader::next_box"): (
        "part2_box_reader_next", _coverage_call("super::box_read_outcome", r"\1"),
        _coverage_call("super::box_reader_state", _coverage_call("final", "self")),
        _coverage_call("super::box_reader_state", _coverage_call("old", "self")),
    ),
    ("src/jp2/box_reader.rs", "box_reader_from_input"): (
        "part2_box_reader_from_input", _coverage_call("super::box_reader_outcome", r"\1"), None,
        r"input@\s*,\s*\*\s*limits",
    ),
    ("src/jp2/box_reader.rs", "required_box"): (
        "part2_box_reader_required", _coverage_call("super::required_box_outcome", r"\1"),
        _coverage_call("super::box_reader_state", _coverage_call("final", "reader")),
        _coverage_call("super::box_reader_state", _coverage_call("old", "reader")) + r"\s*,\s*expected_index",
    ),
    ("src/jp2/box_reader.rs", "read_box_type_at"): (
        "part2_box_type_at", r"\1", None, r"payload@\s*,\s*position\s*,\s*offset",
    ),
}
_BOX_READER_MODELS = {("specs/jp2_box_reader.rs", name) for name in (
    "part2_box_reader_from_input", "part2_box_reader_next", "part2_box_reader_next_ref",
    "part2_box_reader_after_work", "part2_box_reader_after_header", "part2_box_reader_required",
    "part2_box_type_at", "part2_box_u32", "part2_box_u64",
)}
_BOX_READER_PROOFS = {("src/jp2/proof_support.rs", name) for name in (
    "box_reader_state", "box_reader_input_reference", "box_header_view", "box_reference_view",
    "box_read_outcome", "box_ref_outcome", "box_reader_outcome", "required_box_outcome", "box_type_from_bytes_model",
)}
_JPX_INSPECTION_ENTRY = "part2-complete-native-parsed-file-inspection-result"
_JPX_INSPECTION_CONTRACTS = {
    ("src/jpx/inspection.rs", "inspect_file"): (
        "part2_inspect_jpx_file", _coverage_call("inspection_result", r"\1"), None,
        _coverage_call("inspection_file_input", "file") + r"\s*,\s*"
        + _coverage_call("inspection_source_geometries", "codestreams@") + r"\s*,\s*"
        + _coverage_call("crate::limits::resource_frame_limit", "limits"),
    ),
    ("src/jpx/inspection.rs", "effective_layer_count"): (
        "effective_jpx_layer_count", r"\1", None,
        _coverage_call("jp2::source_file_layers", "file") + r"\s*\.len\(\)\s*,\s*"
        + _coverage_call("jp2::jpx_file_decode_view", "file") + r"\s*\.1\.len\(\)",
    ),
}
_RAW_JPX_INSPECTION_ENTRY = "part2-complete-native-raw-public-jpx-inspection-result"
_RAW_JPX_INSPECTION_APIS = {("src/jpx/inspection.rs", "inspect_jpx_layers")}
_RAW_JPX_INSPECTION_CONTRACTS = {
    ("src/jpx/inspection.rs", "inspect_file"): _JPX_INSPECTION_CONTRACTS[("src/jpx/inspection.rs", "inspect_file")],
    ("src/jpx/inspection.rs", "inspect_jpx_layers"): (
        "part2_inspect_raw_jpx_layers", _coverage_call("super::raw_jpx_inspection_outcome", r"\1"), None,
        r"input\s*@\s*,\s*limits",
    ),
}
_RAW_JPX_INSPECTION_MODELS = {
    ("specs/jpx_raw_inspection.rs", name) for name in (
        "part2_inspect_raw_jpx_layers", "part2_ensure_raw_jpx", "part2_raw_inspection_file",
        "part2_raw_inspection_layer", "part2_raw_inspection_composition", "part2_raw_inspection_geometries",
        "part2_raw_timeline_sets", "part2_raw_timeline_instruction",
    )
} | {
    ("specs/jp2_inspection.rs", "part2_parse_and_inspect_container"),
    ("specs/jpx_inspection.rs", "part2_inspect_jpx_file"),
}
_RAW_JPX_INSPECTION_PROOFS = {
    ("src/jpx/proof_support.rs", name) for name in (
        "raw_jpx_inspection_outcome", "raw_jpx_inspection_outcome_known", "raw_jpx_file_known",
        "raw_jpx_composition_known", "raw_jpx_geometries_known",
        "inspection_file_input", "inspection_source_geometries", "timeline_set_views",
    )
} | {
    ("specs/jpx_raw_inspection.rs", "part2_inspect_raw_jpx_layers_unfold"),
    ("src/jp2/proof_support.rs", "raw_jpx_inspection_parts_known"),
    ("src/jp2/proof_support.rs", "raw_jpx_inspection_layer_known"),
    ("src/jp2/proof_support.rs", "raw_inspected_file_reference"),
    ("src/jp2/proof_support.rs", "raw_inspected_native_infos"),
    ("src/jp2/container.rs", "InspectedJp2::file"),
    ("src/jp2/container.rs", "InspectedJp2::codestreams"),
    *_RAW_JPX_INSPECTION_APIS,
}
_JPX_INSPECTION_MODELS = {("specs/jpx_inspection.rs", name) for name in (
    "part2_inspect_jpx_file", "part2_inspection_layer_count", "part2_inspection_layer",
    "part2_inspection_layer_value", "part2_inspection_registration_prefix", "part2_inspection_registration_step",
    "part2_inspection_layers_prefix", "part2_inspection_duration_prefix", "part2_inspection_composition",
)} | {("specs/mod.rs", "effective_jpx_layer_count")}
_JPX_INSPECTION_PROOFS = {("specs/jpx_inspection.rs", name) for name in (
    "part2_inspection_registrations_step", "part2_inspection_registrations_error",
    "part2_inspection_layers_step", "part2_inspection_layers_error",
    "part2_inspection_durations_step", "part2_inspection_durations_error",
)} | {("src/jpx/proof_support.rs", name) for name in (
    "inspection_file_input", "inspection_source_geometries", "inspection_result",
    "inspected_layer_view", "inspected_composition_view",
)} | {("src/jp2/proof_support.rs", "source_layer_reference_known")}
_SOURCE_FRAME_ENTRY = "part2-complete-native-source-frame-result"
_SOURCE_FRAME_CONTRACTS = {
    ("src/jpx/render.rs", "render_inspected_frame"): (
        "part2_render_inspected_source_frame", _coverage_call("crate::color::converted_image_result", r"\1"), None,
        _coverage_call("jp2::jpx_file_decode_view", "file") + r"\s*,\s*"
        + _coverage_call("jp2::source_file_layer_configs", "file") + r"\s*,\s*"
        + _coverage_call("inspection_composition_view", "metadata") + r"\s*,\s*requested_frame\s*,\s*"
        + _coverage_call("crate::options::decode_options_limits", "options"),
    ),
    ("src/jpx/layer_decode.rs", "OwnedLayer::into_image"): (
        "part2_owned_layer_image", _coverage_call("crate::color::converted_image_result", r"\1"), None,
        _coverage_call("owned_layer_view", r"&\s*self"),
    ),
}
_SOURCE_FRAME_MODELS = {("specs/jpx_frame.rs", name) for name in (
    "part2_render_inspected_source_frame", "part2_frame_source_supplies", "part2_owned_layer_image",
)} | {("specs/jpx_dispatch.rs", "part2_decode_effective_layer"),
      ("specs/mod.rs", "part2_render_normalized_frame")}
_SOURCE_FRAME_PROOFS = {("specs/jpx_frame.rs", name) for name in (
    "part2_frame_source_supplies_step", "part2_frame_source_supplies_stopped",
)} | {("src/jpx/proof_support.rs", name) for name in (
    "supplied_views_push", "composition_source_view", "composition_source_frames",
    "inspection_composition_reference", "inspection_composition_view", "instruction_source_layer_index",
)}
_EFFECTIVE_LAYER_ENTRY = "part2-complete-native-effective-layer-result"
_EFFECTIVE_LAYER_CONTRACTS = {
    ("src/jpx/layer_decode.rs", "decode_effective_layer"): (
        "part2_decode_effective_layer", _coverage_call("owned_layer_outcome", r"\1"), None,
        _coverage_call("jp2::jpx_file_decode_view", "file") + r"\s*,\s*"
        + _coverage_call("jp2::source_file_layer_configs", "file") + r"\s*,\s*layer_index\s*,\s*"
        + _coverage_call("crate::options::decode_options_limits", "options"),
    ),
    ("src/jpx/layer_decode.rs", "decode_compositing_layer"): (
        "part2_decode_compositing_layer", _coverage_call("owned_layer_outcome", r"\1"), None,
        _coverage_call("jp2::jpx_file_decode_view", "file") + r"\s*,\s*"
        + _coverage_call("jp2::general_layer_config", "file", "layer") + r"\s*,\s*"
        + _coverage_call("jp2::source_layer_color_override", "layer") + r"\s*,\s*"
        + _coverage_call("jp2::source_layer_geometry", "layer") + r"\s*,\s*layer_index\s*,\s*"
        + _coverage_call("crate::options::decode_options_limits", "options"),
    ),
}
_RAW_RENDER_ENTRY = "part2-complete-native-public-raw-layer-frame-results"
_RAW_RENDER_APIS = {("src/jpx/render.rs", name) for name in ("render_jpx_layer", "render_jpx_frame")}
_RAW_RENDER_CONTRACTS = {
    ("src/jpx/render.rs", "render_jpx_layer"): (
        "part2_render_raw_jpx_layer", _coverage_call("crate::color::converted_image_result", r"\1"), None,
        r"input\s*@\s*,\s*layer_index\s*,\s*" + _coverage_call("crate::options::decode_options_limits", "options"),
    ),
    ("src/jpx/render.rs", "render_jpx_frame"): (
        "part2_render_raw_jpx_frame", _coverage_call("crate::color::converted_image_result", r"\1"), None,
        r"input\s*@\s*,\s*frame_index\s*,\s*" + _coverage_call("crate::options::decode_options_limits", "options"),
    ),
    ("src/jpx/render.rs", "render_inspected_frame"): _SOURCE_FRAME_CONTRACTS[("src/jpx/render.rs", "render_inspected_frame")],
    ("src/jpx/layer_decode.rs", "OwnedLayer::into_image"): _SOURCE_FRAME_CONTRACTS[("src/jpx/layer_decode.rs", "OwnedLayer::into_image")],
    ("src/jpx/layer_decode.rs", "decode_effective_layer"): _EFFECTIVE_LAYER_CONTRACTS[("src/jpx/layer_decode.rs", "decode_effective_layer")],
}
_RAW_RENDER_MODELS = {("specs/jpx_raw_frame.rs", name) for name in (
    "part2_render_raw_jpx_layer", "part2_render_raw_jpx_frame", "part2_raw_associated_header",
    "part2_raw_codestream_source", "part2_raw_jpx_decode_input", "part2_raw_layer_routing", "part2_raw_layer_routings",
)} | {
    ("specs/jp2_inspection.rs", "part2_parse_and_inspect_container"),
    ("specs/jpx_raw_inspection.rs", "part2_ensure_raw_jpx"),
    ("specs/jpx_raw_inspection.rs", "part2_raw_inspection_file"),
    ("specs/jpx_raw_inspection.rs", "part2_raw_inspection_geometries"),
    ("specs/jpx_inspection.rs", "part2_inspect_jpx_file"),
    ("specs/jpx_frame.rs", "part2_render_inspected_source_frame"),
    ("specs/jpx_frame.rs", "part2_owned_layer_image"),
    ("specs/jpx_dispatch.rs", "part2_decode_effective_layer"),
}
_RAW_RENDER_PROOFS = {("src/jp2/proof_support.rs", name) for name in (
    "raw_render_header_known", "raw_render_stream_known", "raw_render_layer_known", "raw_render_file_known",
    "raw_inspected_file_reference", "raw_inspected_native_infos",
)} | {("src/jpx/proof_support.rs", name) for name in (
    "raw_jpx_inspection_outcome_known", "raw_jpx_file_known", "raw_jpx_geometries_known", "raw_jpx_render_metadata_known",
)} | {
    ("specs/jpx_raw_frame.rs", "part2_render_raw_jpx_layer_unfold"),
    ("specs/jpx_raw_frame.rs", "part2_render_raw_jpx_frame_unfold"),
    *_RAW_RENDER_APIS,
}
_RAW_CONTAINER_IMAGE_ENTRY = "part2-complete-native-public-raw-container-image-results"
_RAW_CONTAINER_IMAGE_APIS = {("src/decode/api.rs", name) for name in (
    "decode_jp2", "decode_jp2_selected", "decode_jph", "decode_jph_selected",
)}
_RAW_CONTAINER_IMAGE_CONTRACTS = {
    **{
        ("src/decode/api.rs", name): (
            "part2_decode_raw_single_container", _coverage_call("crate::image::decoded_typed_image_outcome", r"\1"), None,
            r"input\s*@\s*,\s*" + _coverage_call("crate::options::decode_options_limits", "options")
            + r"\s*,\s*" + (_coverage_call("Some", "selection") if selected else "None")
            + r"\s*,\s*" + ("true" if jph else "false"),
        ) for name, selected, jph in (
            ("decode_jp2", False, False), ("decode_jp2_selected", True, False),
            ("decode_jph", False, True), ("decode_jph_selected", True, True),
        )
    },
    **{key: _RAW_INSPECTED_CONTRACTS[key] for key in (
        ("src/jp2/container.rs", "parse_and_inspect"), ("src/jp2/container.rs", "inspect_jph"),
        ("src/jp2/container.rs", "parse_and_inspect_for_display"),
    )},
    ("src/decode/api.rs", "validate_jp2_display_profile"): (
        "part2_validate_jp2_display_profile", r"\1", None,
        _coverage_call("jp2::raw_jp2_file_view", "file"),
    ),
    **{key: _RAW_TYPED_CONTRACTS[key] for key in (
        ("src/decode/api.rs", "decode_codestream"), ("src/decode/api.rs", "decode_codestream_selected"),
    )},
    ("src/decode/output.rs", "apply_jp2_output"): (
        "part2_apply_output_header", _coverage_call("crate::image::decoded_typed_image_outcome", r"\1"), None,
        _coverage_call("crate::image::typed_image_value_view", "decoded") + r"\s*,\s*"
        + _coverage_call("jp2::output_header_view", "header") + r"\s*,\s*"
        + _coverage_call("crate::limits::resource_component_limit", "limits") + r"\s*,\s*"
        + _coverage_call("crate::limits::resource_decoded_bytes_limit", "limits"),
    ),
}
_RAW_CONTAINER_IMAGE_MODELS = {
    ("specs/container_images.rs", "part2_decode_raw_single_container"),
    ("specs/jp2_inspection.rs", "part2_parse_and_inspect_container_mode"),
    ("specs/jp2_inspection.rs", "part2_validate_jp2_display_profile"),
    ("specs/jp2_inspection.rs", "part2_parse_and_inspect_container"),
    ("specs/jp2_inspection.rs", "part2_inspect_jph_container"),
    ("specs/raw_decode.rs", "part2_decode_raw_codestream"),
    ("specs/jpx_raw_frame.rs", "part2_raw_associated_header"),
    ("specs/mod.rs", "part2_apply_output_header"),
}
_RAW_CONTAINER_IMAGE_PROOFS = {
    ("specs/container_images.rs", "part2_decode_raw_single_container_unfold"),
    ("src/jp2/proof_support.rs", "raw_render_file_known"),
    ("src/jp2/proof_support.rs", "raw_inspected_file_reference"),
    *_RAW_CONTAINER_IMAGE_APIS,
} | {("src/jp2/container.rs", name) for name in (
    "InspectedJp2::file", "Jp2File::header", "Jp2File::codestream", "Jp2File::codestream_count",
    "Jp2File::file_type", "CodestreamBox::data", "FileType::is_compatible_with",
)}
_RAW_CONTAINER_IMAGE_TESTS = {("src/decode/container_image_result_tests.rs", "actual_raw_container_image_" + name) for name in (
    "derives_signed_unsigned_full_and_reduced_planes",
    "preserves_requested_tiles_regions_origins_and_selected_limits",
    "applies_complete_palette_mapping_and_channel_definitions",
    "jph_keeps_cleanup_refinement_signedness_and_public_selection",
    "preserves_raw_parse_selection_and_packet_first_errors",
    "checks_inspection_before_brand_count_and_backend",
)} | {("src/decode/tests.rs", "sarah_dev_457acab2c3_later_jp2_streams_do_not_change_first_display")}
_RAW_CONTAINER_COLOR_ENTRY = "part2-complete-native-public-raw-container-color-results"
_RAW_CONTAINER_COLOR_APIS = {("src/decode/api.rs", name) for name in (
    "decode_jp2_color", "decode_jp2_color_selected", "decode_jph_color", "decode_jph_color_selected",
)}
_RAW_CONTAINER_COLOR_CONTRACTS = {
    **{
        ("src/decode/api.rs", name): (
            "part2_decode_raw_color_container", _coverage_call("crate::color::converted_image_result", r"\1"), None,
            r"input\s*@\s*,\s*" + _coverage_call("crate::options::decode_options_limits", "options")
            + r"\s*,\s*" + (_coverage_call("Some", _coverage_call("crate::options::decode_selection_view", "selection")) if selected else "None")
            + r"\s*,\s*" + ("true" if jph else "false"),
        ) for name, selected, jph in (
            ("decode_jp2_color", False, False), ("decode_jp2_color_selected", True, False),
            ("decode_jph_color", False, True), ("decode_jph_color_selected", True, True),
        )
    },
    **{key: value for key, value in _RAW_CONTAINER_IMAGE_CONTRACTS.items() if key not in _RAW_CONTAINER_IMAGE_APIS},
    ("src/decode/output.rs", "color_selection"): (
        "part2_color_selection_raw", _coverage_call("color_selection_outcome", r"\1"), None,
        r"input\s*@\s*,\s*limits\s*,\s*" + _coverage_call("crate::options::decode_selection_view", "requested"),
    ),
    ("src/decode/output.rs", "finish_associated_selected_output"): (
        "part2_finish_associated_selected_output", _coverage_call("crate::color::converted_image_result", r"\1"), None,
        _coverage_call("crate::image::typed_image_value_view", "decoded") + r"\s*,\s*"
        + _coverage_call("jp2::associated_header_option", "header") + r"\s*,\s*target\s*,\s*"
        + _coverage_call("crate::limits::resource_component_limit", "limits") + r"\s*,\s*"
        + _coverage_call("crate::limits::resource_decoded_bytes_limit", "limits") + r"\s*,\s*"
        + _coverage_call("crate::limits::resource_work_limit", "limits"),
    ),
    ("src/color/conversion.rs", "convert_jp2_color"): _JPX_LAYER_COLOR_CONTRACTS[("src/color/conversion.rs", "convert_jp2_color")],
}
_RAW_CONTAINER_COLOR_MODELS = {("specs/container_colors.rs", name) for name in (
    "part2_decode_raw_color_container", "part2_decode_file_color", "part2_color_selection_raw", "part2_color_selection_layout",
)} | {("specs/decoder_input.rs", name) for name in (
    "part2_decoder_input_from_raw", "part2_decode_layout_selected_input", "part2_decode_layout_selected_value_input",
    "part2_decode_typed_layout_input", "part2_decode_typed_layout_value_input",
)} | {
    ("specs/raw_decode.rs", "part2_decode_raw_codestream"),
    ("specs/raw_decode.rs", "part2_decode_raw_codestream_value"),
    ("specs/jp2_inspection.rs", "part2_parse_and_inspect_container_mode"),
    ("specs/jp2_inspection.rs", "part2_validate_jp2_display_profile"),
    ("specs/jp2_inspection.rs", "part2_parse_and_inspect_container"),
    ("specs/jp2_inspection.rs", "part2_inspect_jph_container"),
    ("specs/jpx_raw_frame.rs", "part2_raw_associated_header"),
    ("specs/mod.rs", "part2_color_selection_requested"),
    ("specs/mod.rs", "part2_finish_associated_selected_output"),
    ("specs/mod.rs", "part2_apply_output_header"),
    ("specs/mod.rs", "color_convert_jp2"),
}
_RAW_CONTAINER_COLOR_PROOFS = {
    *_RAW_CONTAINER_COLOR_APIS,
    ("specs/container_colors.rs", "part2_decode_raw_color_container_unfold"),
    ("specs/container_colors.rs", "part2_color_selection_raw_unfold"),
    ("specs/raw_decode.rs", "part2_decode_raw_codestream_selection_value"),
    ("src/jp2/proof_support.rs", "raw_render_file_known"),
    ("src/jp2/proof_support.rs", "raw_inspected_file_reference"),
    ("src/codestream/decoder_input_proof_support.rs", "decoder_layout_input_matches_raw"),
    ("src/codestream/decoder_input_proof_support.rs", "decoder_layout_input_fields"),
    ("src/codestream/proof_support.rs", "selection_geometry_known_fields"),
    ("src/decode/proof_support.rs", "color_selection_outcome"),
    ("src/options.rs", "decode_selection_view"),
}
_RAW_CONTAINER_COLOR_TESTS = {("src/decode/container_image_result_tests.rs", "actual_raw_container_color_" + name) for name in (
    "derives_complete_full_and_reduced_signed_unsigned_gray_planes",
    "jph_preserves_real_cleanup_refinement_and_signed_normalization",
    "derives_expanded_source_context_and_exact_requested_crop",
    "keeps_palette_rgb_and_straight_premultiplied_alpha_metadata",
    "preserves_header_mapping_before_color_admission",
    "preserves_raw_inspection_selection_packet_and_profile_priority",
)} | {("src/decode/tests.rs", "sarah_dev_457acab2c3_later_jp2_streams_do_not_change_first_display")}
_JPIP_PHASE_ENTRY = "part9-complete-nonowning-automatic-phase-results"
_JPIP_PHASE_CONTRACTS = {
    ("src/jpip/automatic_phases.rs", "write_automatic_ordinal"): (
        "part2_jpip_ordinal_cell_phase", r"\1", r"\*\s*" + _coverage_call("final", "slot"),
        r"\*\s*" + _coverage_call("old", "slot") + r"\s*,\s*sequence",
    ),
    ("src/jpip/automatic_phases.rs", "build_automatic_order"): (
        "part2_jpip_order_phase", r"\1",
        _coverage_call("crate::packet::progression_packet_iterator_view", _coverage_call("final", "iterator"))
        + r"\s*,\s*" + _coverage_call("final", "ordinals")
        + r"@\s*\.\s*map_values\s*\(\s*\|row:\s*Vec<Option<u16>>\|\s*row@\s*\)"
        + r"\s*,\s*" + _coverage_call("final", "order") + r"@",
        _coverage_call("crate::decode::progression_plan_view", "plan") + r"\.grid\s*,\s*"
        + _coverage_call("crate::packet::progression_packet_iterator_view", _coverage_call("old", "iterator"))
        + r"\s*,\s*" + _coverage_call("old", "ordinals")
        + r"@\s*\.\s*map_values\s*\(\s*\|row:\s*Vec<Option<u16>>\|\s*row@\s*\)"
        + r"\s*,\s*" + _coverage_call("old", "order") + r"@\s*,\s*0\s*,\s*"
        + _coverage_call("crate::limits::resource_work_limit", "limits"),
    ),
    ("src/jpip/automatic_phases.rs", "decode_automatic_precinct"): (
        "part2_jpip_precinct_phase", r"\1",
        _coverage_call("crate::decode::progression_plan_view", _coverage_call("final", "plan")),
        _coverage_call("crate::decode::progression_plan_view", _coverage_call("old", "plan"))
        + r"\s*,\s*execution\s*,\s*template\s*,\s*prefix@\s*,\s*start\s*,\s*sequence\s*,\s*layer\s*,\s*limits",
    ),
    ("src/jpip/automatic_phases.rs", "emit_automatic_tile_part"): (
        "part2_jpip_emit_part_phase", r"\1", _coverage_call("final", "bytes") + r"@",
        _coverage_call("old", "bytes") + r"@\s*,\s*"
        + _coverage_call("super::jpip_automatic_tile_part_view", "part") + r"\s*,\s*available_layers",
    ),
}
_JPIP_BYTE_RESULT_ENTRY = "part9-complete-native-word-template-results"
_JPIP_BYTE_RESULT_CONTRACTS = {
    ("src/jpip/byte_io.rs", "write_u32_be"): (
        "part2_jpip_write_u32", r"\1", _coverage_call("final", "output") + r"\s*@",
        _coverage_call("old", "output") + r"@\s*,\s*position\s*,\s*value",
    ),
    ("src/jpip/automatic_headers.rs", "append_empty_packet"): (
        "part2_jpip_append_empty_packet", r"\1", _coverage_call("final", "output") + r"\s*@",
        _coverage_call("old", "output") + r"@\s*,\s*sop\s*,\s*eph\s*,\s*sequence",
    ),
    ("src/jpip/automatic_headers.rs", "build_automatic_transition_template"): (
        "part2_jpip_transition_template", _coverage_call("jpip_packet_bytes_outcome", r"\1"), None,
        r"main@\s*,\s*" + _coverage_call("tile_headers@.map_values",
            r"\|parts:\s*Vec<Vec<u8>>\|\s*" + _coverage_call("parts@.map_values",
                r"\|header:\s*Vec<u8>\|\s*header@")) + r"\s*,\s*limits",
    ),
    ("src/jpip/automatic_headers.rs", "build_automatic_template"): (
        "part2_jpip_flat_template", _coverage_call("jpip_packet_bytes_outcome", r"\1"), None,
        r"main@\s*,\s*" + _coverage_call("tile_headers@.map_values",
            r"\|header:\s*Vec<u8>\|\s*header@") + r"\s*,\s*limits",
    ),
}
_JPIP_BYTE_RESULT_MODELS = {
    "part2_jpip_u32_bytes": ("(value >> 24)", "(value >> 16)", "(value >> 8)", "(value & 0xff)"),
    "part2_jpip_write_u32_end": (
        "position as nat + 4 > usize::MAX as nat",
        "{ usize::MAX as nat } else { position as nat + 4 }",
    ),
    "part2_jpip_write_u32": (
        "part2_jpip_write_u32_end(position)", "position as nat > end || end > before.len()",
        "MalformedKind::Truncated)), before)", "if count == 4 { Ok(()) }",
        "before.subrange(0, position as int)", "part2_jpip_u32_bytes(value).subrange(0, count as int)",
        "before.subrange(end as int, before.len() as int)",
    ),
    "part2_jpip_empty_packet_bytes": (
        "if sop", "((sequence >> 8) & 0xff) as u8", "(sequence & 0xff) as u8",
        "seq![0u8]", "if eph { seq![0xffu8, 0x92u8] }",
    ),
    "part2_jpip_append_empty_packet": (
        "(Ok(()), before + part2_jpip_empty_packet_bytes(sop, eph, sequence))",
    ),
    "part2_jpip_template_append": (
        "header.len() > u32::MAX as nat", "before.len() + 6 > usize::MAX as nat",
        "part2_jpip_write_u32(before + header, (before.len() + 6) as usize, header.len() as u32)",
        "match written.0 { Err(error) => Err(error), Ok(()) => Ok(written.1) }",
    ),
    "part2_jpip_template_finish": (
        "output + seq![0xffu8, 0xd9u8]",
        "bytes.len() as u64 > crate::limits::resource_input_byte_limit(limits)",
        "resource: crate::Resource::InputBytes",
        "limit: crate::limits::resource_input_byte_limit(limits), actual: bytes.len() as u64",
    ),
    "part2_jpip_transition_template_fold": (
        "if tile >= headers.len() { part2_jpip_template_finish(output, limits) }",
        "part2_jpip_transition_template_fold(headers, tile + 1, 0, output, limits)",
        "part2_jpip_template_append(output, headers[tile as int][part as int])",
        "Err(error) => Err(error)",
        "part2_jpip_transition_template_fold(headers, tile, part + 1, next, limits)",
    ),
    "part2_jpip_transition_template": ("part2_jpip_transition_template_fold(headers, 0, 0, main, limits)",),
    "part2_jpip_flat_template_fold": (
        "if index >= headers.len() { part2_jpip_template_finish(output, limits) }",
        "part2_jpip_template_append(output, headers[index as int])", "Err(error) => Err(error)",
        "part2_jpip_flat_template_fold(headers, index + 1, next, limits)",
    ),
    "part2_jpip_flat_template": ("part2_jpip_flat_template_fold(headers, 0, main, limits)",),
}
_JPIP_BYTE_RESULT_TESTS = {("src/jpip/normalization_result_tests.rs", name) for name in (
    "checked_word_writes_preserve_big_endian_bytes_errors_and_every_outside_byte",
    "checked_empty_packets_preserve_prefix_framing_sequence_and_storage",
    "automatic_templates_preserve_all_parts_psot_bytes_and_patch_before_final_limit_errors",
)}
_JPIP_AUTOMATIC_INPUT_ENTRY = "part9-complete-native-automatic-header-partition-inputs"
_JPIP_AUTOMATIC_INPUT_CONTRACTS = {
    ("src/jpip/mapping.rs", "siz_cardinality"): (
        "part2_jpip_siz_cardinality", r"\1", None, r"main_header@\s*,\s*limits",
    ),
    ("src/jpip/automatic_headers.rs", "ceil_div_jpip"): (
        "part2_jpip_ceil_div", r"\1", None, r"value\s*,\s*divisor",
    ),
    ("src/jpip/automatic_headers.rs", "partition_automatic_tile_parts"): (
        "part2_jpip_partition_automatic_tiles", _coverage_call("jpip_automatic_partition_outcome", r"\1"), None,
        _coverage_call("headers@.map_values", r"\|header:\s*Vec<u8>\|\s*header@")
        + r"\s*,\s*" + _coverage_call("states@.map_values",
            r"\|state:\s*&crate::codestream::TilePartPayload<'_>\|\s*"
            + _coverage_call("crate::codestream::tile_part_owned_view", "state"))
        + r"\s*,\s*" + _coverage_call("transitions@.map_values",
            r"\|transition:\s*JpipTilePartTransition\|\s*" + _coverage_call("jpip_transition_view", "&transition"))
        + r"\s*,\s*" + _coverage_call("jpip_automatic_packets_view", "packets"),
    ),
}
_JPIP_PLACEHOLDER_ENTRY = "part9-native-placeholder-representation-selection"
_JPIP_PLACEHOLDER_CONTRACTS = {
    ("src/jpip/reconstruction.rs", "parse_jpip_placeholder"): (
        "part2_jpip_parse_placeholder", _coverage_call("placeholder_parse_outcome", r"\1"), None, r"payload@",
    ),
    ("src/jpip/byte_io.rs", "read_u64_be"): (
        "part2_jpip_read_u64", r"\1", None, r"input@\s*,\s*position",
    ),
    ("src/jpip/reconstruction.rs", "placeholder_reconstruction"): (
        "part2_jpip_placeholder_reconstruction",
        _coverage_call("placeholder_reconstruction_outcome", r"\1"), None,
        r"flags\s*,\s*original@\s*,\s*"
        + _coverage_call("placeholder_header_option_view", "equivalent"),
    ),
}
_JPIP_PLACEHOLDER_IMPLEMENTATIONS = set(_JPIP_PLACEHOLDER_CONTRACTS) | {
    ("src/jpip/reconstruction.rs", "DatabinCache::expand_metadata_bin"),
    ("src/jp2/box_reader.rs", "BoxType::new"),
}
_JPIP_PLACEHOLDER_BODY_CLAUSE = (
    "vstd::prelude::ensures(|result: Self| { "
    "vstd::prelude::equal(result, super::box_type_from_bytes_model(bytes)) && "
    "vstd::prelude::equal(result, super::box_type_from_word_model(crate::specs::part2_box_u32(bytes))) });"
)
_JPIP_PLACEHOLDER_MODELS = {("specs/jpip_layout.rs", name) for name in (
    "part2_jpip_placeholder_reconstruction", "part2_jpip_parse_placeholder",
    "part2_jpip_placeholder_header", "part2_jpip_placeholder_equivalent", "part2_jpip_placeholder_stream",
)} | {("specs/jpip_transitions.rs", "part2_jpip_read_u64")} | {
    ("src/jp2/proof_support.rs", name) for name in (
        "box_type_from_bytes_model", "box_type_from_word_model",
    )
}
_JPIP_PLACEHOLDER_PROOFS = set(_JPIP_PLACEHOLDER_CONTRACTS) | {
    ("src/jpip/reconstruction.rs", name) for name in (
        "placeholder_source_view", "placeholder_header_option_view", "placeholder_reconstruction_outcome",
        "placeholder_value_view", "placeholder_parse_outcome",
    )
} | {
    ("src/jp2/proof_support.rs", "box_type_from_bytes_word"),
    ("src/jp2/box_reader.rs", "BoxType::new"),
}
_JPIP_PLACEHOLDER_TESTS = {("src/jpip/tests.rs", name) for name in (
    "semantic_equivalent_metadata_preserves_declared_representation",
    "semantic_original_metadata_precedes_available_equivalent_representation",
    "placeholder_reconstruction_preserves_raw_precedence_and_header_owners",
    "placeholder_parser_accepts_standard_bit_flags_and_types_extensions",
    "placeholder_raw_results_preserve_every_field_and_first_error",
)}
_JPIP_LAYOUT_ENTRY = "part9-complete-native-public-layout-results"
_JPIP_LAYOUT_CONTRACTS = {
    ("src/jpip/reconstruction.rs", name): (
        model, _coverage_call("jpip_byte_outcome", r"\1"), None,
        _coverage_call("jpip_cache_view", "self") + r"\s*,\s*" + _coverage_call("jpip_layout_view", "layout"),
    )
    for name, model in (
        ("DatabinCache::reconstruct_codestream", "part2_jpip_cache_codestream"),
        ("DatabinCache::reconstruct_container", "part2_jpip_cache_container"),
    )
}
_JPIP_LAYOUT_APIS = set(_JPIP_LAYOUT_CONTRACTS)
_JPIP_LAYOUT_CONTRACTS[("src/jpip/cache.rs", "DatabinCache::reconstruct")] = (
    "part2_jpip_cache_reconstruct", _coverage_call("jpip_byte_outcome", r"\1"), None,
    _coverage_call("jpip_cache_view", "self") + r"\s*,\s*" + _coverage_call("jpip_layout_view", "layout"),
)
_JPIP_LAYOUT_CONTRACTS[("src/jpip/message.rs", "parse_data_after_identity")] = (
    "part2_jpip_data_after_identity", _coverage_call("jpip_message_outcome", r"\1"), None,
    r"input\s*@\s*,\s*position\s*,\s*" + _coverage_call("databin_id_view", "databin")
    + r"\s*,\s*last_byte\s*,\s*limits",
)
_JPIP_LAYOUT_IMPLEMENTATIONS = _JPIP_LAYOUT_APIS | {("src/jpip/message.rs", "parse_jpip_message")}
_JPIP_LAYOUT_MODELS = {("specs/jpip_layout.rs", name) for name in (
    "part2_jpip_layout_error", "part2_jpip_codestream_pairs", "part2_jpip_codestream_markers",
    "part2_jpip_cache_codestream", "part2_jpip_metadata_layout", "part2_jpip_cache_container",
)} | {("specs/jpip_cache_views.rs", "part2_jpip_cache_reconstruct")} | {
    ("specs/jpip_message.rs", "part2_jpip_data_after_identity"),
    ("specs/jpip_message.rs", "part2_jpip_data_identity_cut"),
}
_JPIP_LAYOUT_PROOFS = set(_JPIP_LAYOUT_CONTRACTS) | {
    ("src/jpip/cache.rs", "DatabinCache::reconstruct"),
    ("src/jpip/proof_support.rs", "databin_id_view"),
    ("src/jpip/message.rs", "parse_jpip_message"),
    ("specs/jpip_message.rs", "part2_jpip_data_identity_cut"),
    ("specs/jpip_cache_views.rs", "part2_jpip_cache_reconstruct"),
} | {("src/jpip/cache_proof_support.rs", name) for name in (
    "jpip_cache_view", "jpip_layout_view", "jpip_byte_view", "jpip_byte_outcome",
)}
_JPIP_LAYOUT_TESTS = {("src/jpip/cache_layout_result_tests.rs", name) for name in (
    "actual_jpip_layout_results_preserve_shape_classes_pair_order_and_error_precedence",
    "actual_jpip_layout_results_derive_arbitrary_cache_bytes_limits_markers_and_native_frames",
    "actual_jpip_layout_results_compose_owned_insertion_and_keep_as_implemented_marker_admission",
)}
_JPIP_CACHE_INSERT_ENTRY = "part9-complete-native-cache-insert-result"
_JPIP_CACHE_INSERT_CONTRACTS = {
    ("src/jpip/cache.rs", "DatabinCache::insert"): (
        "part2_jpip_cache_insert", r"\1",
        _coverage_call("jpip_cache_view", _coverage_call("final", "self")),
        _coverage_call("jpip_cache_view", _coverage_call("old", "self"))
        + r"\s*,\s*" + _coverage_call("jpip_fragment_view", r"&\s*fragment"),
    ),
}
_JPIP_CACHE_INSERT_MODELS = {("specs/jpip_cache_insert.rs", name) for name in (
    "part2_jpip_insert_overflow", "part2_jpip_insert_conflict", "part2_jpip_insert_first",
    "part2_jpip_insert_overlap", "part2_jpip_insert_merge", "part2_jpip_insert_replaced",
    "part2_jpip_insert_copy", "part2_jpip_insert_copy_stored", "part2_jpip_insert_normalize",
    "part2_jpip_insert_commit", "part2_jpip_insert_incoming_copy", "part2_jpip_insert_stored_copy",
    "part2_jpip_insert_account", "part2_jpip_insert_sum", "part2_jpip_insert_finish",
    "part2_jpip_insert_merge_result", "part2_jpip_insert_first_result", "part2_jpip_insert_final_scan",
    "part2_jpip_insert_final_state", "part2_jpip_insert_bin_remaining", "part2_jpip_insert_bin",
    "part2_jpip_insert_result", "part2_jpip_cache_insert",
)} | {
    ("specs/jpip_fragment.rs", "part2_jpip_find_databin"),
    ("specs/jpip_fragment.rs", "part2_jpip_stored_end"),
    ("specs/jpip_fragment.rs", "part2_jpip_copy_into"),
    ("specs/mod.rs", "part9_standard_class_assigned"),
}
_JPIP_CACHE_INSERT_PROOFS = set(_JPIP_CACHE_INSERT_CONTRACTS) | {
    ("src/jpip/cache.rs", "Databin::validate_final_length"),
    ("src/jpip/cache.rs", "Databin::normalize_fragments"),
    ("src/jpip/cache.rs", "DatabinCache::find_databin_index"),
    ("src/jpip/cache.rs", "StoredFragment::end"),
    ("src/jpip/cache.rs", "copy_into"),
    ("src/jpip/cache.rs", "conflict"),
    ("src/jpip.rs", "Databin::clone"),
    ("src/jpip.rs", "StoredFragment::clone"),
    ("src/limits.rs", "resource_input_byte_limit"),
    ("src/limits.rs", "resource_jpip_fragment_limit"),
} | {("src/jpip/cache_proof_support.rs", name) for name in (
    "jpip_fragment_view", "jpip_cache_view", "jpip_databin_view", "jpip_stored_fragment_view",
    "jpip_stored_parts", "jpip_stored_parts_fields", "jpip_fragment_fields",
    "jpip_cache_fields", "jpip_databin_fields",
)} | {("specs/jpip_cache_insert.rs", name) for name in (
    "part2_jpip_insert_bin_remaining_unfold", "part2_jpip_insert_final_scan_extent",
    "part2_jpip_insert_result_unfold", "part2_jpip_cache_insert_error_frame",
    "part2_jpip_insert_first_bounds", "part2_jpip_insert_merge_bounds",
)} | {("src/refinement/jpip.rs", name) for name in (
    "jpip_overlap_consistent", "jpip_final_length_consistent", "jpip_merge_start",
    "jpip_merge_end", "jpip_transaction_commit",
)}
_JPIP_CACHE_INSERT_TESTS = {("src/jpip/cache_insert_result_tests.rs", name) for name in (
    "sarah_metadata_target_identity_preserves_sparse_union_and_error_frames",
    "actual_jpip_cache_insert_checked_clones_preserve_fields_and_independent_storage",
    "actual_jpip_cache_insert_errors_preserve_complete_physical_state_and_error_precedence",
    "actual_jpip_cache_insert_normalizes_exact_bytes_and_retains_first_alias_metadata",
    "reserved_wire_classes_cannot_mutate_recognized_or_physical_cache_state",
)}
_JPIP_CACHE_INSERT_IMPLEMENTATIONS = set(_JPIP_CACHE_INSERT_CONTRACTS) | {
    ("src/jpip/cache.rs", "Databin::validate_final_length"),
    ("src/jpip/cache.rs", "Databin::normalize_fragments"),
    ("src/jpip/message.rs", "ingest_jpip_response"),
}
_JPIP_CACHE_VIEW_ENTRY = "part9-complete-native-cache-view-results"
_JPIP_CACHE_VIEW_CONTRACTS = {
    ("src/jpip/cache.rs", name): (
        model, projection, None,
        _coverage_call("jpip_cache_view", "self") + r"\s*,\s*" + inputs,
    )
    for name, model, projection, inputs in (
        ("DatabinCache::status", "part2_jpip_cache_status", _coverage_call("jpip_status_outcome", r"\1"), _coverage_call("databin_id_view", "id")),
        ("DatabinCache::is_complete", "part2_jpip_cache_complete", r"\1", _coverage_call("databin_id_view", "id")),
        ("DatabinCache::databin_view", "part2_jpip_cache_view", _coverage_call("jpip_byte_outcome", r"\1"), _coverage_call("databin_id_view", "id")),
        ("DatabinCache::databin_prefix", "part2_jpip_cache_prefix", r"\1\s*@", _coverage_call("databin_id_view", "id")),
        ("DatabinCache::reconstruct", "part2_jpip_cache_reconstruct", _coverage_call("jpip_byte_outcome", r"\1"), _coverage_call("jpip_layout_view", "layout")),
    )
}
_JPIP_CACHE_VIEW_MODELS = {("specs/jpip_cache_views.rs", name) for name in (
    "part2_jpip_cache_error", "part2_jpip_status_scan", "part2_jpip_databin_status",
    "part2_jpip_cache_status", "part2_jpip_cache_complete", "part2_jpip_cache_view",
    "part2_jpip_cache_prefix", "part2_jpip_reconstruct_prefix", "part2_jpip_flatten_prefix",
    "part2_jpip_cache_reconstruct",
)} | {
    ("specs/jpip_fragment.rs", "part2_jpip_find_databin"),
    ("specs/jpip_fragment.rs", "part2_jpip_stored_end"),
    ("specs/jpip_fragment.rs", "part2_jpip_status_complete"),
    ("specs/mod.rs", "part9_reconstruction_length"),
}
_JPIP_CACHE_VIEW_PROOFS = set(_JPIP_CACHE_VIEW_CONTRACTS) | {
    ("src/jpip/cache.rs", "DatabinCache::find_databin_index"),
    ("src/jpip/cache.rs", "StoredFragment::end"),
    ("src/jpip/cache.rs", "DatabinStatus::is_complete"),
    ("src/jpip/cache.rs", "JpipByteView::into_bytes"),
    ("src/jpip/proof_support.rs", "databin_id_view"),
    ("src/refinement/jpip.rs", "jpip_reconstruction_length"),
    ("src/limits.rs", "resource_input_byte_limit"),
    ("specs/jpip_cache_views.rs", "part2_jpip_reconstruct_error_persists"),
} | {("src/jpip/cache_proof_support.rs", name) for name in (
    "jpip_cache_view", "jpip_databin_view", "jpip_stored_fragment_view", "jpip_status_view",
    "jpip_byte_view", "jpip_byte_outcome", "jpip_status_outcome", "jpip_layout_view",
    "jpip_view_parts", "jpip_cache_fields", "jpip_databin_fields", "jpip_status_fields",
)}
_JPIP_CACHE_VIEW_TESTS = {("src/jpip/cache_view_result_tests.rs", name) for name in (
    "actual_jpip_cache_status_derives_every_field_and_native_fragment_order_without_validity_premises",
    "actual_jpip_cache_view_keeps_first_normalized_match_first_fragment_and_exact_missing_errors",
    "actual_jpip_cache_prefix_derives_first_fragment_offset_and_keeps_independent_owned_storage",
    "actual_jpip_cache_reconstruction_keeps_requested_order_repetition_and_original_cache_storage",
    "actual_jpip_cache_reconstruction_preserves_first_view_error_and_exact_input_budget_frontiers",
    "actual_jpip_cache_read_producers_compose_original_fragment_normalization_and_reconstruction",
)}
_JPIP_CACHE_VIEW_CALLERS = {
    ("src/jpip/reconstruction.rs", "DatabinCache::reconstruct_codestream"),
    ("src/jpip/reconstruction.rs", "DatabinCache::reconstruct_container"),
    ("src/jpip/progression.rs", "DatabinCache::build_automatic_snapshot"),
}
_JPIP_FRAGMENT_ENTRY = "part9-complete-native-owned-entry-foundations"
_JPIP_FRAGMENT_CONTRACTS = {
    ("src/jpip/cache.rs", "copy_bytes"): (
        "part2_jpip_copy_bytes", r"\1\s*@", None, r"input\s*@",
    ),
    ("src/jpip/cache.rs", "copy_into"): (
        "part2_jpip_copy_into", r"\1", _coverage_call("final", "output") + r"\s*@",
        _coverage_call("old", "output") + r"\s*@\s*,\s*output_start\s*,\s*input\s*@\s*,\s*error_offset",
    ),
    ("src/jpip/cache.rs", "DatabinCache::find_databin_index"): (
        "part2_jpip_find_databin", r"\1", None,
        _coverage_call("jpip_cache_view", "self") + r"\.1\s*,\s*" + _coverage_call("databin_id_view", "id") + r"\s*,\s*0",
    ),
}
_JPIP_FRAGMENT_BODY_CLAUSES = {
    "JpipFragment::new": "vstd::prelude::ensures(|result: Result<Self, DecodeError>| vstd::prelude::equal(jpip_fragment_outcome(result), jpip_fragment_new_input(databin, offset, &bytes, is_final, auxiliary, limits)));",
    "JpipFragment::from_message": "vstd::prelude::ensures(|result: Result<Self, DecodeError>| vstd::prelude::equal(jpip_fragment_outcome(result), jpip_fragment_message_input(header, body, limits)));",
    "DatabinCache::new": "vstd::prelude::ensures(|result: Self| vstd::prelude::equal(jpip_cache_view(&result), crate::specs::part2_jpip_empty_cache(limits)));",
}
_JPIP_FRAGMENT_GETTERS = {
    "JpipFragment::databin": "databin_id_view(result) == jpip_fragment_view(self).0",
    **{name: f"result == jpip_fragment_view(self).{field}" for name, field in (
        ("JpipFragment::offset", 1), ("JpipFragment::final_length", 3), ("JpipFragment::auxiliary", 4),
    )},
    "JpipFragment::bytes": "result@ == jpip_fragment_view(self).2",
    "StoredFragment::end": "result == crate::specs::part2_jpip_stored_end(jpip_stored_fragment_view(self))",
    **{name: f"result == jpip_status_view(self).{field}" for name, field in (
        ("DatabinStatus::final_length", 0), ("DatabinStatus::contiguous_prefix", 1),
        ("DatabinStatus::stored_bytes", 2), ("DatabinStatus::interval_count", 3),
    )},
    "DatabinStatus::is_complete": "result == crate::specs::part2_jpip_status_complete(jpip_status_view(self))",
    "JpipByteView::as_bytes": "result@ == jpip_byte_view(self)",
    "JpipByteView::len": "result as nat == jpip_byte_view(self).len()",
    "JpipByteView::is_empty": "result == (jpip_byte_view(self).len() == 0)",
    "JpipByteView::into_bytes": "result@ == jpip_byte_view(&self), result == *jpip_byte_storage(&self)",
    "JpipByteView::as_ref": "result@ == jpip_byte_view(self)",
    "DatabinCache::stored_bytes": "result == jpip_cache_view(self).2",
    "DatabinCache::accepted_fragments": "result == jpip_cache_view(self).3",
    "DatabinCache::databin_count": "result as nat == jpip_cache_view(self).1.len()",
}
_JPIP_FRAGMENT_MODELS = {("specs/jpip_fragment.rs", name) for name in (
    "part2_jpip_fragment_new", "part2_jpip_fragment_from_message", "part2_jpip_stored_end",
    "part2_jpip_copy_bytes", "part2_jpip_copy_into", "part2_jpip_empty_cache", "part2_jpip_find_databin",
    "part2_jpip_status_complete",
)} | {
    ("specs/jpip_message.rs", "part2_jpip_identity"), ("specs/mod.rs", "valid_jpip_fragment"),
    ("specs/mod.rs", "complete_jpip_databin"),
}
_JPIP_FRAGMENT_PROOFS = {("src/jpip/cache.rs", name) for name in (*_JPIP_FRAGMENT_BODY_CLAUSES, *_JPIP_FRAGMENT_GETTERS)} | {
    ("src/jpip/proof_support.rs", "databin_id_view"), ("src/jpip/proof_support.rs", "jpip_header_view"),
} | {("src/jpip/cache_proof_support.rs", name) for name in (
    "jpip_fragment_view", "jpip_fragment_outcome", "jpip_fragment_new_input", "jpip_fragment_message_input",
    "jpip_stored_fragment_view", "jpip_databin_view", "jpip_cache_view", "jpip_status_view",
    "jpip_byte_view", "jpip_byte_storage", "jpip_fragment_fields", "jpip_cache_fields", "jpip_status_fields",
)}
_JPIP_FRAGMENT_TESTS = {("src/jpip/cache_entry_result_tests.rs", name) for name in (
    "actual_jpip_owned_fragment_derives_all_fields_and_moves_original_bytes_across_raw_frontiers",
    "actual_jpip_owned_fragment_from_header_preserves_length_validation_and_owned_payload",
    "actual_jpip_byte_copy_and_point_copy_preserve_full_outside_frames_and_every_error",
    "actual_jpip_cache_empty_state_and_lookup_preserve_first_normalized_databin_identity",
    "actual_jpip_stored_extent_and_status_getters_retain_saturation_and_exact_completeness",
    "actual_jpip_owned_byte_view_getters_and_move_keep_original_storage_without_cloning",
)}
_JPIP_MESSAGE_ENTRY = "part9-complete-native-raw-message-results"
_JPIP_MESSAGE_BOUNDARIES = {("src/jpip/message.rs", "JpipMessageParser::parse")}
_JPIP_MESSAGE_CONTRACTS = {
    ("src/jpip/message.rs", "parse_jpip_message"): (
        "part2_parse_jpip_message", _coverage_call("jpip_message_outcome", r"\1"),
        _coverage_call("jpip_context_view", r"\*\s*" + _coverage_call("final", "context")),
        r"input\s*@\s*,\s*" + _coverage_call("jpip_context_view", r"\*\s*" + _coverage_call("old", "context")) + r"\s*,\s*limits",
    ),
    ("src/jpip/message.rs", "JpipMessageParser::parse"): (
        "part2_jpip_parser_parse", _coverage_call("jpip_message_outcome", r"\1"),
        _coverage_call("jpip_parser_view", _coverage_call("final", "self")),
        r"input\s*@\s*,\s*" + _coverage_call("jpip_parser_view", _coverage_call("old", "self")),
    ),
    ("src/jpip/message.rs", "parse_end_of_response"): (
        "part2_jpip_eor", _coverage_call("jpip_message_outcome", r"\1"), None, r"input\s*@",
    ),
    ("src/jpip/message.rs", "read_vbas"): (
        "part2_jpip_read_vbas", r"\1", r"\*\s*" + _coverage_call("final", "position"),
        r"input\s*@\s*,\s*\*\s*" + _coverage_call("old", "position") + r"\s*,\s*first_mask",
    ),
}
_JPIP_MESSAGE_BODY_CLAUSES = {
    "DatabinClass::from_identifier": "vstd::prelude::ensures(|result: Option<Self>| vstd::prelude::equal(result, crate::specs::part2_jpip_class(identifier)));",
    "DatabinClass::has_auxiliary": "vstd::prelude::ensures(|result: bool| vstd::prelude::equal(result, crate::specs::part2_jpip_auxiliary(identifier)));",
    "DatabinId::new": "vstd::prelude::ensures(|result: Result<Self, DecodeError>| vstd::prelude::equal(databin_id_outcome(result), crate::specs::part2_jpip_databin(class_identifier, codestream, in_class)));",
    "DatabinId::from_wire": "vstd::prelude::ensures(|result: Result<Self, DecodeError>| vstd::prelude::equal(databin_id_outcome(result), crate::specs::part2_jpip_wire_databin(class_identifier, codestream, in_class)));",
    **{name: f"vstd::prelude::ensures(|result: {kind}| vstd::prelude::equal(result, databin_id_view(*self).{field}));"
       for name, kind, field in (
           ("DatabinId::class_identifier", "u64", 0), ("DatabinId::class", "DatabinClass", 1),
           ("DatabinId::codestream", "u64", 2), ("DatabinId::in_class", "u64", 3),
       )},
    "DatabinId::same_as": "vstd::prelude::ensures(|result: bool| vstd::prelude::equal(result, crate::specs::part2_jpip_identity(databin_id_view(*self), databin_id_view(other))));",
    "JpipHeaderContext::new": "vstd::prelude::ensures(|result: Self| jpip_context_view(result) == (None, None));",
    **{name: f"vstd::prelude::ensures(|result: Option<u64>| result == jpip_context_view(*self).{field});"
       for name, field in (("JpipHeaderContext::previous_class", 0), ("JpipHeaderContext::previous_codestream", 1))},
    "JpipMessageParser::new": "vstd::prelude::ensures(|result: Self| vstd::prelude::equal(jpip_parser_context(&result), (None, None)) && vstd::prelude::equal(*jpip_parser_limits(&result), limits));",
}
_JPIP_MESSAGE_GETTERS = {
    "JpipMessageHeader::databin": "databin_id_view(result) == jpip_header_view(*self).0",
    **{name: f"result == jpip_header_view(*self).{field}" for name, field in (
        ("JpipMessageHeader::offset", 1), ("JpipMessageHeader::length", 2), ("JpipMessageHeader::is_last_byte", 3),
        ("JpipMessageHeader::auxiliary", 4), ("JpipMessageHeader::header_length", 5),
    )},
    "JpipMessageHeader::final_length": "result == crate::specs::part2_jpip_final_length(jpip_header_view(*self))",
    "JpipEndOfResponse::reason_code": "result == jpip_eor_view(self).0",
    "JpipEndOfResponse::body": "result == jpip_eor_body_reference(self), result@ == jpip_eor_view(self).1",
    "JpipEndOfResponse::header_length": "result == jpip_eor_view(self).2",
    "JpipMessage::body": "result == jpip_message_body_reference(self)",
    "JpipMessageParser::context": "jpip_context_view(result) == jpip_parser_context(self)",
}
_JPIP_MESSAGE_MODELS = {("specs/jpip_message.rs", name) for name in (
    "part2_parse_jpip_message", "part2_jpip_parser_parse", "part2_jpip_data", "part2_jpip_data_after_identity",
    "part2_jpip_eor", "part2_jpip_body", "part2_jpip_read_vbas", "part2_jpip_vbas_tail",
    "part2_jpip_class", "part2_jpip_databin", "part2_jpip_wire_databin", "part2_jpip_auxiliary", "part2_jpip_identity", "part2_jpip_final_length",
)} | {("specs/mod.rs", name) for name in (
    "part9_header_form_valid", "part9_header_has_explicit_class", "part9_header_has_explicit_codestream",
    "part9_vbas_step", "part9_auxiliary_present", "part9_eor_extent",
    "part9_class_identifier_valid", "part9_standard_class_assigned", "part9_class_key", "part9_databin_identity",
)}
_JPIP_MESSAGE_PROOFS = {
    ("specs/jpip_message.rs", "part2_parse_jpip_message_unfold"),
    *_JPIP_MESSAGE_BOUNDARIES,
    *{("src/jpip/message.rs", name) for name in (*_JPIP_MESSAGE_BODY_CLAUSES, *_JPIP_MESSAGE_GETTERS)},
} | {("src/jpip/proof_support.rs", name) for name in (
    "databin_id_view", "databin_id_outcome", "jpip_context_view", "jpip_parser_context", "jpip_parser_limits",
    "jpip_parser_view", "jpip_context_fields", "jpip_parser_fields", "jpip_header_view", "jpip_message_view",
    "jpip_message_outcome", "jpip_message_body_reference", "jpip_eor_view", "jpip_eor_body_reference",
    "jpip_message_values_known", "jpip_header_fields",
)}
_JPIP_MESSAGE_TESTS = {("src/jpip/message_result_tests.rs", name) for name in (
    "sarah_metadata_target_identity_retains_raw_codestream_fields",
    "sarah_reserved_classes_have_no_registered_header_semantics",
    "semantic_identity_aliases_only_assigned_auxiliary_classes",
    "actual_raw_jpip_vbas_matches_independent_values_and_partial_cursor_on_every_error",
    "actual_raw_jpip_data_derives_all_header_fields_body_borrow_and_consumed_extent",
    "actual_raw_jpip_inherited_context_commits_only_complete_data_messages",
    "actual_raw_jpip_eor_and_prefix_bodies_preserve_context_and_original_borrowed_slices",
    "actual_raw_jpip_rejects_overflow_extent_and_limit_frontiers_in_native_order",
    "actual_raw_jpip_databin_and_header_getters_preserve_normalized_identity_and_saturating_final_length",
    "sarah_dev_9a1abe441f_bounded_vbas_padding_preserves_values_and_delimiters",
    "sarah_dev_9a1abe441f_padded_message_fields_preserve_context_and_body",
    "sarah_initial_history_defaults_preserve_absence_and_effective_identifiers",
    "sarah_initial_history_defaults_commit_only_after_complete_data",
    "sarah_initial_history_defaults_are_response_local_not_cache_history",
)}
_JPIP_RESPONSE_ENTRY = "part9-complete-native-raw-response-result"
_JPIP_RESPONSE_APIS = {("src/jpip/message.rs", "ingest_jpip_response")}
_JPIP_RESPONSE_CONTRACTS = {
    ("src/jpip/message.rs", "ingest_jpip_response"): (
        "part2_ingest_jpip_response", _coverage_call("jpip_response_outcome", r"\1"),
        _coverage_call("jpip_cache_view", _coverage_call("final", "cache")),
        r"input\s*@\s*,\s*" + _coverage_call("jpip_cache_view", _coverage_call("old", "cache")),
    ),
    ("src/jpip/message.rs", "JpipMessageParser::parse"):
        _JPIP_MESSAGE_CONTRACTS[("src/jpip/message.rs", "JpipMessageParser::parse")],
    ("src/jpip/cache.rs", "DatabinCache::insert"):
        _JPIP_CACHE_INSERT_CONTRACTS[("src/jpip/cache.rs", "DatabinCache::insert")],
}
_JPIP_RESPONSE_MODELS = {("specs/jpip_response.rs", name) for name in (
    "part2_jpip_response_data", "part2_jpip_response_remaining", "part2_ingest_jpip_response",
)} | {
    ("specs/jpip_message.rs", "part2_jpip_parser_parse"),
    ("specs/jpip_message.rs", "part2_parse_jpip_message"),
    ("specs/jpip_fragment.rs", "part2_jpip_fragment_from_message"),
    ("specs/jpip_cache_insert.rs", "part2_jpip_cache_insert"),
}
_JPIP_RESPONSE_GETTERS = {
    "JpipResponseSummary::messages": ("self.messages", "0"),
    "JpipResponseSummary::end_of_response_reason": ("self.end_of_response_reason", "1"),
}
_JPIP_RESPONSE_PROOFS = set(_JPIP_RESPONSE_CONTRACTS) | {
    ("src/jpip/cache.rs", "JpipFragment::from_message"),
    ("src/jpip/message.rs", "parse_jpip_message"),
    ("src/jpip/proof_support.rs", "jpip_parser_context"),
    ("src/jpip/proof_support.rs", "jpip_parser_limits"),
    ("src/jpip/proof_support.rs", "jpip_message_values_known"),
    ("src/jpip/proof_support.rs", "jpip_header_fields"),
} | {("src/jpip/message.rs", name) for name in _JPIP_RESPONSE_GETTERS} | {
    ("src/jpip/cache_proof_support.rs", name) for name in (
        "jpip_cache_view", "jpip_cache_fields", "jpip_response_summary_view", "jpip_response_outcome",
    )
}
_JPIP_RESPONSE_TESTS = {("src/jpip/response_result_tests.rs", name) for name in (
    "actual_jpip_response_derives_full_summary_and_cache_from_raw_header_forms_and_eor",
    "actual_jpip_response_retains_exact_prior_commits_and_relative_errors_at_every_raw_cut",
    "actual_jpip_response_preserves_first_limit_overflow_error_and_native_cache_frames",
)}
_JPIP_RANGE_ENTRY = "part9-complete-native-range-availability-byte-results"
_JPIP_RANGE_APIS = {("src/jpip/ranges.rs", "DatabinCache::availability")}
_JPIP_RANGE_CONTRACTS = {
    ("src/jpip/ranges.rs", name): (model, projection, None,
        _coverage_call("jpip_cache_view", "self") + r"\s*,\s*" + inputs)
    for name, model, projection, inputs in (
        ("DatabinCache::availability", "part2_jpip_cache_availability",
         _coverage_call("jpip_availability_outcome", r"\1"), _coverage_call("jpip_ranges_view", "ranges")),
        ("DatabinCache::complete_databin_missing", "part2_jpip_complete_missing",
         _coverage_call("jpip_missing_views", r"&\s*\1"), _coverage_call("databin_id_view", "id")),
        ("DatabinCache::read_packet_ranges", "part2_jpip_read_packets",
         _coverage_call("jpip_packet_bytes_outcome", r"\1"), _coverage_call("jpip_packets_view", "packets")),
    )
}
_JPIP_RANGE_CALLERS = {
    ("src/jpip/reconstruction.rs", "DatabinCache::expand_metadata_bin"),
    ("src/jpip/ranges.rs", "DatabinCache::precinct_availability"),
    ("src/jpip/ranges.rs", "DatabinCache::progressive_availability"),
    ("src/jpip/precinct.rs", "DatabinCache::reconstruct_precinct_packets"),
    ("src/jpip/precinct.rs", "DatabinCache::transcode_precinct_codestream"),
}
_JPIP_RANGE_MODELS = {("specs/jpip_ranges.rs", name) for name in (
    "part2_jpip_range_overflow", "part2_jpip_range_new", "part2_jpip_complete_missing",
    "part2_jpip_missing_total", "part2_jpip_availability_finish", "part2_jpip_availability_fragments",
    "part2_jpip_availability_request", "part2_jpip_availability_remaining", "part2_jpip_cache_availability",
    "part2_jpip_packet_total", "part2_jpip_packet_fragments", "part2_jpip_packet_remaining", "part2_jpip_read_packets",
)}
_JPIP_RANGE_BODY_CLAUSES = {
    "JpipDatabinRange::new": "vstd::prelude::ensures(|result: Result<Self, DecodeError>| { vstd::prelude::equal(jpip_range_outcome(result), crate::specs::part2_jpip_range_new(databin_id_view(databin), offset, length)) });",
    "JpipDatabinRange::databin": "vstd::prelude::ensures(|result: DatabinId| { vstd::prelude::equal(databin_id_view(result), jpip_range_view(*self).0) });",
    "JpipDatabinRange::offset": "vstd::prelude::ensures(|result: u64| { vstd::prelude::equal(result, jpip_range_view(*self).1) });",
    "JpipDatabinRange::length": "vstd::prelude::ensures(|result: u64| { vstd::prelude::equal(result, jpip_range_view(*self).2) });",
}
_JPIP_RANGE_GETTERS = {name: clause for name, clause in (
    ("JpipMissingRange::databin", "databin_id_view(result) == jpip_missing_view(*self).0"),
    ("JpipMissingRange::offset", "result == jpip_missing_view(*self).1"),
    ("JpipMissingRange::length", "result == jpip_missing_view(*self).2"),
    ("JpipAvailabilityReport::status", "result == jpip_availability_view(self).0"),
    ("JpipAvailabilityReport::required_bytes", "result == jpip_availability_view(self).1"),
    ("JpipAvailabilityReport::available_bytes", "result == jpip_availability_view(self).2"),
    ("JpipAvailabilityReport::missing_ranges", "result@.map_values(|range: JpipMissingRange| jpip_missing_view(range)) == jpip_availability_view(self).3"),
    ("JpipAvailabilityReport::is_available", "result == matches!(jpip_availability_view(self).0, JpipAvailability::Available)"),
)}
_JPIP_RANGE_PROJECTIONS = {("src/jpip/range_proof_support.rs", name) for name in (
    "jpip_range_view", "jpip_range_outcome", "jpip_ranges_view", "jpip_missing_view", "jpip_missing_views",
    "jpip_availability_view", "jpip_availability_outcome", "jpip_packet_view", "jpip_packets_view", "jpip_packet_bytes_outcome",
)}
_JPIP_RANGE_PROOFS = set(_JPIP_RANGE_CONTRACTS) | _JPIP_RANGE_PROJECTIONS | {
    ("src/jpip/ranges.rs", name) for name in (*_JPIP_RANGE_BODY_CLAUSES, *_JPIP_RANGE_GETTERS, "append_missing_ranges")
} | {
    ("src/jpip/cache.rs", "DatabinCache::find_databin_index"),
    ("src/jpip/cache.rs", "DatabinCache::status"), ("src/jpip/cache.rs", "StoredFragment::end"),
    ("src/jpip/cache_proof_support.rs", "jpip_cache_fields"), ("src/jpip/cache_proof_support.rs", "jpip_databin_fields"),
    ("src/limits.rs", "resource_input_byte_limit"), ("src/limits.rs", "resource_packet_limit"),
    ("src/limits.rs", "resource_work_limit"), ("src/refinement/jpip.rs", "jpip_available_bytes"),
}
_JPIP_RANGE_TESTS = {("src/jpip/range_result_tests.rs", name) for name in (
    "actual_jpip_range_entries_missing_tails_and_getters_retain_exact_native_fields",
    "actual_jpip_availability_derives_ordered_missing_work_and_all_error_frontiers_without_cache_premises",
    "actual_jpip_packet_bytes_keep_raw_order_repetition_saturation_priorities_and_original_cache_storage",
)}
_JPIP_PLANNED_ENTRY = "part9-complete-native-owned-plan-packet-results"
_JPIP_PLANNED_APIS = {("src/jpip/precinct.rs", "DatabinCache::reconstruct_precinct_packets")}
_JPIP_PLANNED_CONTRACTS = {
    ("src/jpip/precinct.rs", "DatabinCache::reconstruct_precinct_packets"): (
        "part2_jpip_planned_packets", _coverage_call("jpip_planned_packets_outcome", r"\1"), None,
        _coverage_call("jpip_cache_view", "self") + r"\s*,\s*" + _coverage_call("jpip_plan_view", "plan") + r"\s*,\s*layers",
    ),
}
_JPIP_PLANNED_CONTRACTS.update({
    ("src/jpip/ranges.rs", name): _JPIP_RANGE_CONTRACTS[("src/jpip/ranges.rs", name)]
    for name in ("DatabinCache::availability", "DatabinCache::read_packet_ranges")
})
_JPIP_PLANNED_MODELS = {("specs/jpip_planned_packets.rs", name) for name in (
    "part2_jpip_plan_invalid", "part2_jpip_packet_new", "part2_jpip_plan_layer_packets",
    "part2_jpip_plan_layers", "part2_jpip_plan_new", "part2_jpip_plan_packet_end", "part2_jpip_planned_packets",
)} | {
    ("specs/jpip_ranges.rs", "part2_jpip_range_new"),
    ("specs/jpip_ranges.rs", "part2_jpip_cache_availability"),
    ("specs/jpip_ranges.rs", "part2_jpip_read_packets"),
}
_JPIP_PLANNED_BODY_CLAUSES = {
    "JpipPrecinctPacket::new": "vstd::prelude::ensures(|result: Result<Self, DecodeError>| { vstd::prelude::equal(jpip_packet_outcome(result), crate::specs::part2_jpip_packet_new(databin_id_view(databin), layer, offset, length)) });",
    "JpipPrecinctPacket::range": "vstd::prelude::ensures(|result: JpipDatabinRange| { vstd::prelude::equal(jpip_range_view(result), jpip_packet_view(*self).0) });",
    "JpipPrecinctPacket::layer": "vstd::prelude::ensures(|result: u16| { vstd::prelude::equal(result, jpip_packet_view(*self).1) });",
    "JpipPrecinctCodestreamPlan::new": "vstd::prelude::ensures(|result: Result<Self, DecodeError>| { vstd::prelude::equal(jpip_plan_outcome(result), crate::specs::part2_jpip_plan_new(databin_id_view(main_header), databin_id_view(tile_header), jpip_owned_packets_view(&packets), layers, limits)) && match result { Err(_) => true, Ok(value) => vstd::prelude::equal(*jpip_plan_packet_owner(&value), packets), } });",
    "JpipPrecinctCodestreamPlan::main_header": "vstd::prelude::ensures(|result: DatabinId| { vstd::prelude::equal(databin_id_view(result), jpip_plan_view(self).0) });",
    "JpipPrecinctCodestreamPlan::tile_header": "vstd::prelude::ensures(|result: DatabinId| { vstd::prelude::equal(databin_id_view(result), jpip_plan_view(self).1) });",
    "JpipPrecinctCodestreamPlan::packets": "vstd::prelude::ensures(|result: &[JpipPrecinctPacket]| { vstd::prelude::equal(jpip_packets_view(result), jpip_plan_view(self).2) });",
    "JpipPrecinctCodestreamPlan::layers": "vstd::prelude::ensures(|result: u16| { vstd::prelude::equal(result, jpip_plan_layer_count(self)) });",
    "JpipPrecinctCodestreamPlan::packet_end_for_layers": "vstd::prelude::ensures(|result: Result<usize, DecodeError>| { vstd::prelude::equal(result, crate::specs::part2_jpip_plan_packet_end(jpip_plan_view(self), layers)) });",
}
_JPIP_PLANNED_PROJECTIONS = {("src/jpip/plan_proof_support.rs", name) for name in (
    "jpip_packet_outcome", "jpip_owned_packets_view", "jpip_plan_view", "jpip_plan_packet_owner",
    "jpip_plan_layer_count", "jpip_plan_outcome", "jpip_planned_packets_view", "jpip_planned_availability_owner",
    "jpip_planned_packet_owner", "jpip_planned_packets_outcome", "jpip_optional_byte_view",
    "jpip_optional_owned_byte_view", "jpip_plan_fields",
)}
_JPIP_PLANNED_GETTERS = {name: clause for name, clause in (
    ("JpipPrecinctPackets::layers", "result == jpip_planned_packets_view(self).0"),
    ("JpipPrecinctPackets::availability", "jpip_availability_view(result) == jpip_planned_packets_view(self).1"),
    ("JpipPrecinctPackets::packets", "jpip_optional_byte_view(result) == jpip_planned_packets_view(self).2"),
    ("JpipPrecinctPackets::into_packets", "jpip_optional_owned_byte_view(result) == jpip_planned_packets_view(&self).2"),
)}
_JPIP_PLANNED_PROOFS = set(_JPIP_PLANNED_CONTRACTS) | _JPIP_PLANNED_PROJECTIONS | {
    ("src/jpip/precinct.rs", name) for name in (*_JPIP_PLANNED_BODY_CLAUSES, *_JPIP_PLANNED_GETTERS)
} | {
    ("src/jpip/ranges.rs", "JpipDatabinRange::new"),
    ("src/jpip/range_proof_support.rs", "jpip_packet_view"),
    ("src/jpip/range_proof_support.rs", "jpip_range_view"),
    ("src/jpip/range_proof_support.rs", "jpip_availability_view"),
    ("src/limits.rs", "resource_layer_limit"), ("src/limits.rs", "resource_packet_limit"),
    ("src/limits.rs", "resource_input_byte_limit"),
}
_JPIP_PLANNED_TESTS = {("src/jpip/planned_packet_result_tests.rs", name) for name in (
    "actual_jpip_owned_packet_plans_preserve_full_fields_owner_and_first_admission_errors",
    "actual_jpip_planned_packet_results_derive_arbitrary_physical_selection_availability_and_bytes",
    "actual_jpip_planned_packets_compose_raw_ingestion_and_preserve_missing_partial_and_owned_outputs",
)}
_JPIP_TRANSCODE_ENTRY = "part9-complete-native-precinct-transcode-results"
_JPIP_TRANSCODE_APIS = {("src/jpip/precinct.rs", "DatabinCache::transcode_precinct_codestream")}
_JPIP_TRANSCODE_CONTRACTS = {
    ("src/jpip/precinct.rs", "DatabinCache::transcode_precinct_codestream"): (
        "part2_jpip_transcode", _coverage_call("jpip_transcode_outcome", r"\1"), None,
        _coverage_call("jpip_cache_view", "self") + r"\s*,\s*" + _coverage_call("jpip_plan_view", "plan") + r"\s*,\s*layers",
    ),
    ("src/jpip/ranges.rs", "DatabinCache::precinct_availability"): (
        "part2_jpip_precinct_availability", _coverage_call("jpip_availability_outcome", r"\1"), None,
        _coverage_call("jpip_cache_view", "self") + r"\s*,\s*" + _coverage_call("jpip_plan_view", "plan") + r"\s*,\s*packet_end",
    ),
}
_JPIP_TRANSCODE_CONTRACTS.update({
    ("src/jpip/ranges.rs", name): _JPIP_RANGE_CONTRACTS[("src/jpip/ranges.rs", name)]
    for name in ("DatabinCache::availability", "DatabinCache::read_packet_ranges")
})
_JPIP_TRANSCODE_CONTRACTS[("src/jpip/cache.rs", "DatabinCache::databin_view")] = (
    _JPIP_CACHE_VIEW_CONTRACTS[("src/jpip/cache.rs", "DatabinCache::databin_view")]
)
_JPIP_TRANSCODE_MODELS = {("specs/jpip_transcode.rs", name) for name in (
    "part2_jpip_append_complete_requirement", "part2_jpip_precinct_availability",
    "part2_jpip_patch_cod_loop", "part2_jpip_patch_cod", "part2_jpip_patch_main",
    "part2_jpip_patch_tile", "part2_jpip_validate_precinct_raw", "part2_jpip_validate_precinct",
    "part2_jpip_transcode_bytes", "part2_jpip_transcode_payload", "part2_jpip_transcode",
)} | {
    ("specs/jpip_planned_packets.rs", "part2_jpip_plan_packet_end"),
    ("specs/jpip_ranges.rs", "part2_jpip_cache_availability"),
    ("specs/jpip_ranges.rs", "part2_jpip_read_packets"),
    ("specs/jpip_cache_views.rs", "part2_jpip_cache_status"),
    ("specs/jpip_cache_views.rs", "part2_jpip_cache_view"),
    ("specs/raw_layout.rs", "part1_parse_layout"),
}
_JPIP_TRANSCODE_FRAMES = {
    ("src/jpip/ranges.rs", "DatabinCache::append_complete_databin_requirement"):
        "(result, jpip_availability_view(final(report))) == crate::specs::part2_jpip_append_complete_requirement(jpip_cache_view(self), databin_id_view(id), jpip_availability_view(old(report)))",
    **{("src/jpip/precinct.rs", name): clause for name, clause in (
        ("patch_cod_layers", "(result, final(header)@) == crate::specs::part2_jpip_patch_cod(old(header)@, start, layers, stop_at_sod)"),
        ("validate_and_patch_main_header", "(result, final(header)@) == crate::specs::part2_jpip_patch_main(old(header)@, layers)"),
        ("validate_and_patch_tile_header", "(result, final(header)@) == crate::specs::part2_jpip_patch_tile(old(header)@, layers)"),
        ("validate_precinct_codestream", "result == crate::specs::part2_jpip_validate_precinct(bytes@, layers, limits)"),
        ("JpipPrecinctTranscode::layers", "result == jpip_transcode_view(self).0"),
        ("JpipPrecinctTranscode::availability", "jpip_availability_view(result) == jpip_transcode_view(self).1"),
        ("JpipPrecinctTranscode::codestream", "jpip_optional_byte_view(result) == jpip_transcode_view(self).2"),
        ("JpipPrecinctTranscode::into_codestream", "jpip_optional_owned_byte_view(result) == jpip_transcode_view(&self).2"),
    )},
}
_JPIP_TRANSCODE_PROOFS = set(_JPIP_TRANSCODE_CONTRACTS) | set(_JPIP_TRANSCODE_FRAMES) | {
    ("src/jpip/plan_proof_support.rs", name) for name in (
        "jpip_transcode_view", "jpip_transcode_availability_owner", "jpip_transcode_byte_owner", "jpip_transcode_outcome",
    )
} | {
    ("src/codestream/decoder_input_proof_support.rs", "jpip_precinct_layout_fields"),
    ("specs/jpip_transcode.rs", "part2_jpip_validate_precinct_unfold"),
    ("src/codestream/layout.rs", "parse_layout"),
    ("src/codestream/geometry.rs", "ImageSize::tile_count"),
    ("src/jpip/cache.rs", "DatabinCache::status"),
    ("src/jpip/precinct.rs", "JpipPrecinctCodestreamPlan::packet_end_for_layers"),
}
_JPIP_TRANSCODE_TESTS = {("src/jpip/transcode_result_tests.rs", name) for name in (
    "actual_jpip_cod_header_scans_preserve_exact_patches_and_partial_mutations_at_every_cut",
    "actual_jpip_transcode_composes_raw_responses_to_exact_owned_codestreams_and_public_images",
    "actual_jpip_transcode_preserves_physical_header_layer_limit_and_raw_validation_error_frontiers",
)} | {("src/jpip/transcode_availability_result_tests.rs",
       "actual_jpip_complete_header_requirements_preserve_partial_reports_and_physical_cache_priorities")}
_JPIP_PROGRESSIVE_ENTRY = "part9-complete-native-caller-progressive-results"
_JPIP_PROGRESSIVE_APIS = {("src/jpip/progression.rs", name) for name in (
    "JpipProgressiveDecoder::update", "JpipProgressiveDecoder::update_selected",
)}
_JPIP_PROGRESSIVE_CONTRACTS = {
    ("src/jpip/progression.rs", name): (
        "part2_jpip_progressive_update", _coverage_call("jpip_progressive_outcome", r"\1"),
        _coverage_call("jpip_progressive_decoder_view", _coverage_call("final", "self")),
        _coverage_call("jpip_cache_view", "cache") + r"\s*,\s*"
        + _coverage_call("jpip_progressive_decoder_view", _coverage_call("old", "self"))
        + r"\s*,\s*options\s*,\s*" + selected,
    )
    for name, selected in (
        ("JpipProgressiveDecoder::update", "None"),
        ("JpipProgressiveDecoder::update_selected", _coverage_call("Some", "selection")),
        ("JpipProgressiveDecoder::update_inner", "selection"),
    )
}
_JPIP_PROGRESSIVE_CONTRACTS[("src/jpip/ranges.rs", "DatabinCache::progressive_availability")] = (
    "part2_jpip_progressive_availability", _coverage_call("jpip_progressive_availability_outcome", r"\1"), None,
    _coverage_call("jpip_cache_view", "self") + r"\s*,\s*" + _coverage_call("jpip_plan_view", "plan"),
)
_JPIP_PROGRESSIVE_CONTRACTS[("src/jpip/precinct.rs", "DatabinCache::transcode_precinct_codestream")] = (
    _JPIP_TRANSCODE_CONTRACTS[("src/jpip/precinct.rs", "DatabinCache::transcode_precinct_codestream")]
)
_JPIP_PROGRESSIVE_CONTRACTS.update({
    ("src/decode/api.rs", name): _RAW_TYPED_CONTRACTS[("src/decode/api.rs", name)]
    for name in ("decode_codestream", "decode_codestream_selected")
})
_JPIP_PROGRESSIVE_MODELS = {("specs/jpip_progressive.rs", name) for name in (
    "part2_jpip_progressive_layers", "part2_jpip_progressive_availability", "part2_jpip_progressive_update",
)} | {
    ("specs/jpip_transcode.rs", "part2_jpip_append_complete_requirement"),
    ("specs/jpip_transcode.rs", "part2_jpip_transcode"),
    ("specs/jpip_ranges.rs", "part2_jpip_cache_availability"),
    ("specs/raw_decode.rs", "part2_decode_raw_codestream"),
}
_JPIP_PROGRESSIVE_BODY_CLAUSES = {
    "JpipProgressiveDecoder::new": "vstd::prelude::ensures(|result: Self| { vstd::prelude::equal(jpip_progressive_decoder_view(&result), (jpip_plan_view(&plan), 0_u16)) && vstd::prelude::equal(*jpip_progressive_plan_owner(&result), plan) });",
    "JpipProgressiveDecoder::plan": "vstd::prelude::ensures(|result: &JpipPrecinctCodestreamPlan| { vstd::prelude::equal(jpip_plan_view(result), jpip_progressive_decoder_view(self).0) && vstd::prelude::equal(result, jpip_progressive_plan_owner(self)) });",
    "JpipProgressiveDecoder::decoded_layers": "vstd::prelude::ensures(|result: u16| { vstd::prelude::equal(result, jpip_progressive_decoder_view(self).1) });",
}
_JPIP_PROGRESSIVE_GETTERS = {name: clause for name, clause in (
    ("JpipProgressiveUpdate::status", "result == jpip_progressive_update_view(self).0"),
    ("JpipProgressiveUpdate::previous_layers", "result == jpip_progressive_update_view(self).1"),
    ("JpipProgressiveUpdate::available_layers", "result == jpip_progressive_update_view(self).2"),
    ("JpipProgressiveUpdate::missing_ranges", "result@.map_values(|range: JpipMissingRange| super::jpip_missing_view(range)) == jpip_progressive_update_view(self).3"),
    ("JpipProgressiveUpdate::image", "jpip_optional_image_borrow_view(result) == jpip_progressive_update_view(self).4"),
    ("JpipProgressiveUpdate::into_image", "jpip_optional_image_view(result) == jpip_progressive_update_view(&self).4"),
)}
_JPIP_PROGRESSIVE_PROJECTIONS = {("src/jpip/progression_proof_support.rs", name) for name in (
    "jpip_progressive_decoder_view", "jpip_progressive_plan_owner", "jpip_progressive_update_view",
    "jpip_progressive_image_borrow", "jpip_progressive_image_owner", "jpip_optional_image_view",
    "jpip_optional_image_borrow_view", "jpip_progressive_outcome", "jpip_progressive_availability_outcome",
)}
_JPIP_PROGRESSIVE_PROOFS = set(_JPIP_PROGRESSIVE_CONTRACTS) | _JPIP_PROGRESSIVE_PROJECTIONS | {
    ("src/jpip/progression.rs", name) for name in (*_JPIP_PROGRESSIVE_BODY_CLAUSES, *_JPIP_PROGRESSIVE_GETTERS)
} | {
    ("src/jpip/ranges.rs", "DatabinCache::append_complete_databin_requirement"),
    ("src/jpip/precinct.rs", "JpipPrecinctCodestreamPlan::layers"),
    ("src/jpip/cache.rs", "JpipByteView::as_bytes"),
    ("src/image/proof_support.rs", "decoded_typed_image_outcome"),
    ("src/image/proof_support.rs", "typed_image_value_view"),
    ("src/refinement/jpip.rs", "jpip_progressive_update_valid"),
    ("src/refinement/jpip.rs", "jpip_quality_prefix_available"),
}
_JPIP_PROGRESSIVE_TESTS = {("src/jpip/progressive_result_tests.rs", name) for name in (
    "actual_jpip_progressive_constructor_waiting_protocol_errors_and_plan_owner_are_exact",
    "actual_jpip_progressive_raw_updates_return_complete_images_and_original_optional_image_owners",
    "actual_jpip_progressive_full_selected_decode_errors_preserve_prior_state_and_skip_unneeded_decoding",
)} | {("src/jpip/progressive_availability_result_tests.rs",
       "actual_jpip_progressive_availability_derives_physical_headers_layers_missing_and_narrowing_errors")}
_JPIP_TRANSITION_ENTRY = "part9-complete-native-raw-transition-results"
_JPIP_TRANSITION_APIS = {("src/jpip/mapping.rs", "DatabinCache::tile_part_transitions")}
_JPIP_TRANSITION_CALLERS = {("src/jpip/progression.rs", name) for name in (
    "DatabinCache::build_automatic_snapshot", "DatabinCache::automatic_headers",
)}
_JPIP_TRANSITION_CONTRACTS = {
    ("src/jpip/automatic_headers.rs", "normalize_automatic_tile_headers"): (
        "part2_jpip_normalize_automatic_tile_headers", _coverage_call("jpip_normalized_headers_outcome", r"\1"),
        None, r"input@\s*,\s*tile",
    ),
    ("src/jpip/automatic_headers.rs", "normalize_tile_header"): (
        "part2_jpip_normalize_tile_header", _coverage_call("jpip_packet_bytes_outcome", r"\1"),
        None, r"source@\s*,\s*tile\s*,\s*index\s*,\s*count",
    ),
    ("src/jpip/mapping.rs", "DatabinCache::tile_part_transitions"): (
        "part2_jpip_transition_report", _coverage_call("jpip_transition_report_outcome", r"\1"), None,
        _coverage_call("jpip_cache_view", "self") + r"\s*,\s*codestream\s*,\s*tile",
    ),
    ("src/jpip/mapping.rs", "parse_tile_part_transitions"): (
        "part2_jpip_parse_transitions", _coverage_call("jpip_transitions_outcome", r"\1"), None, r"input@\s*,\s*expected_tile",
    ),
    ("src/jpip/mapping.rs", "count_plt_packets"): ("part2_jpip_plt_count", r"\1", None, r"payload@"),
    ("src/jpip/automatic_headers.rs", "marker_segment"): ("part2_jpip_marker_segment", r"\1", None, r"input@\s*,\s*position"),
    ("src/jpip/byte_io.rs", "read_u16_be"): ("part2_jpip_read_u16", r"\1", None, r"input@\s*,\s*position"),
    ("src/jpip/byte_io.rs", "read_u32_be"): ("part2_jpip_read_u32", r"\1", None, r"input@\s*,\s*position"),
    ("src/jpip/cache.rs", "copy_bytes"): ("part2_jpip_copy_bytes", r"\1\s*@", None, r"input@"),
}
_JPIP_TRANSITION_CONTRACTS.update({
    ("src/jpip/cache.rs", name): _JPIP_CACHE_VIEW_CONTRACTS[("src/jpip/cache.rs", name)]
    for name in ("DatabinCache::is_complete", "DatabinCache::databin_view")
})
_JPIP_TRANSITION_CONTRACTS[("src/jpip/ranges.rs", "DatabinCache::complete_databin_missing")] = (
    _JPIP_RANGE_CONTRACTS[("src/jpip/ranges.rs", "DatabinCache::complete_databin_missing")]
)
_JPIP_TRANSITION_MODELS = {("specs/jpip_transitions.rs", name) for name in (
    "part2_jpip_read_u16", "part2_jpip_read_u32", "part2_jpip_marker_segment", "part2_jpip_plt_scan",
    "part2_jpip_plt_count", "part2_jpip_transition_scan", "part2_jpip_transition_parts",
    "part2_jpip_parse_transitions", "part2_jpip_transition_needs", "part2_jpip_transition_report",
)} | {("specs/jpip_normalization.rs", name) for name in (
    "part2_jpip_normalized_header_scan", "part2_jpip_normalized_header_after_start",
    "part2_jpip_normalize_tile_header", "part2_jpip_normalized_header_entries",
    "part2_jpip_normalize_automatic_tile_headers",
)} | {
    ("specs/jpip_cache_views.rs", "part2_jpip_cache_complete"), ("specs/jpip_cache_views.rs", "part2_jpip_cache_view"),
    ("specs/jpip_ranges.rs", "part2_jpip_complete_missing"), ("specs/jpip_fragment.rs", "part2_jpip_copy_bytes"),
    ("specs/mod.rs", "jpip_tile_transition_sufficient"),
}
_JPIP_TRANSITION_GETTERS = {name: clause for name, clause in (
    ("JpipSemanticNeed::kind", "result == jpip_semantic_need_view(*self).0"),
    ("JpipSemanticNeed::identifier", "result == jpip_semantic_need_view(*self).1"),
    ("JpipTilePartTransition::tile", "result == jpip_transition_view(self).0"),
    ("JpipTilePartTransition::tile_part", "result == jpip_transition_view(self).1"),
    ("JpipTilePartTransition::packet_count", "result == jpip_transition_view(self).2"),
    ("JpipTilePartTransition::data_length", "result == jpip_transition_view(self).3"),
    ("JpipTilePartTransition::has_functional_change", "result == jpip_transition_view(self).4"),
    ("JpipTilePartTransition::header_bytes", "result@ == jpip_transition_view(self).5"),
    ("JpipTilePartTransitionReport::status", "result == jpip_transition_report_view(self).0"),
    ("JpipTilePartTransitionReport::transitions", "result@.map_values(|transition: JpipTilePartTransition| jpip_transition_view(&transition)) == jpip_transition_report_view(self).1"),
    ("JpipTilePartTransitionReport::semantic_needs", "result@.map_values(|need: JpipSemanticNeed| jpip_semantic_need_view(need)) == jpip_transition_report_view(self).2"),
    ("JpipTilePartTransitionReport::missing_ranges", "result@.map_values(|missing: JpipMissingRange| super::jpip_missing_view(missing)) == jpip_transition_report_view(self).3"),
)}
_JPIP_TRANSITION_PROJECTIONS = {("src/jpip/transition_proof_support.rs", name) for name in (
    "jpip_normalized_headers_outcome",
    "jpip_transition_view", "jpip_transitions_view", "jpip_transitions_outcome", "jpip_semantic_need_view",
    "jpip_semantic_needs_view", "jpip_transition_report_view", "jpip_transition_report_outcome",
    "jpip_transition_sequence_shapes",
)}
_JPIP_TRANSITION_PROOFS = set(_JPIP_TRANSITION_CONTRACTS) | _JPIP_TRANSITION_PROJECTIONS | {
    ("src/jpip/mapping.rs", name) for name in _JPIP_TRANSITION_GETTERS
} | {
    ("src/jpip/range_proof_support.rs", "jpip_packet_bytes_outcome"),
    ("src/jpip/message.rs", "DatabinId::new"),
    ("src/jpip/cache.rs", "JpipByteView::into_bytes"),
    ("src/refinement/jpip.rs", "jpip_tile_transition_sufficient"),
}
_JPIP_TRANSITION_TESTS = {("src/jpip/transition_result_tests.rs", name) for name in (
    "sarah_dev_926ef1a301_nonzero_psot_cannot_mean_unknown_length",
    "sarah_dev_dfa2d383b6_public_report_rejects_nonzero_short_psot",
    "actual_jpip_transition_words_markers_and_plt_match_independent_extents_and_counts",
    "actual_jpip_raw_transitions_derive_all_fields_owned_headers_and_exact_emitted_cut_errors",
    "actual_jpip_raw_transition_admission_keeps_native_plt_sod_psot_and_first_error_differences",
    "actual_jpip_public_transition_reports_preserve_physical_cache_needs_getters_and_native_storage",
)} | {("src/jpip/normalization_result_tests.rs", name) for name in (
    "raw_normalization_preserves_exact_markers_framing_optional_sod_and_input_storage",
    "raw_normalization_retains_malformed_marker_and_index_error_precedence",
)} | {("src/jpip/tests.rs", name) for name in (
    "sarah_optional_sod_complete_header_forms_normalize_identically",
    "sarah_optional_sod_public_snapshot_decodes_complete_empty_header",
)}
_RAW_JPX_PUBLIC_IMAGE_ENTRY = "part2-complete-native-public-raw-jpx-codestream-results"
_RAW_JPX_PUBLIC_IMAGE_APIS = {("src/decode/api.rs", name) for name in (
    "decode_jpx_codestream", "decode_jpx_codestream_selected", "decode_jpx_codestream_color", "decode_jpx_codestream_color_selected",
)}
_RAW_JPX_PUBLIC_IMAGE_CONTRACTS = {
    **{
        ("src/decode/api.rs", name): (
            "part2_decode_raw_jpx_color" if color else "part2_decode_raw_jpx_typed",
            _coverage_call("crate::color::converted_image_result" if color else "crate::image::decoded_typed_image_outcome", r"\1"), None,
            r"input\s*@\s*,\s*codestream_index\s*,\s*" + _coverage_call("crate::options::decode_options_limits", "options")
            + r"\s*,\s*" + (_coverage_call("Some", _coverage_call("crate::options::decode_selection_view", "selection")) if selected else "None"),
        ) for name, selected, color in (
            ("decode_jpx_codestream", False, False), ("decode_jpx_codestream_selected", True, False),
            ("decode_jpx_codestream_color", False, True), ("decode_jpx_codestream_color_selected", True, True),
        )
    },
    ("src/jp2/container.rs", "parse"): _RAW_CONTAINER_CONTRACTS[("src/jp2/container.rs", "parse")],
    ("src/decode/output.rs", "decode_jpx_file"): _JPX_SOURCE_CONTRACTS[("src/decode/output.rs", "decode_jpx_file")],
    ("src/decode/output.rs", "decode_jpx_file_selected"): (
        "part2_decode_jpx_selected_file", _coverage_call("associated_typed_outcome", r"\1"), None,
        _coverage_call("jp2::jpx_file_decode_view", "file") + r"\s*,\s*codestream_index\s*,\s*"
        + _coverage_call("crate::options::decode_options_limits", "options") + r"\s*,\s*"
        + _coverage_call("crate::options::decode_selection_view", "selection"),
    ),
    ("src/decode/output.rs", "color_selection"): _RAW_CONTAINER_COLOR_CONTRACTS[("src/decode/output.rs", "color_selection")],
    **{
        ("src/decode/output.rs", name): (
            "part2_convert_associated_selected" if selected else "part2_convert_associated",
            _coverage_call("crate::color::converted_image_result", r"\1"), None,
            _coverage_call("crate::image::typed_image_value_view", r"\*\s*image") + r"\s*,\s*"
            + _coverage_call("jp2::associated_header_option", "header") + (r"\s*,\s*target" if selected else "") + r"\s*,\s*"
            + _coverage_call("crate::limits::resource_decoded_bytes_limit", "limits") + r"\s*,\s*"
            + _coverage_call("crate::limits::resource_work_limit", "limits"),
        ) for name, selected in (("convert_associated_color", False), ("convert_associated_selected_color", True))
    },
    ("src/codestream/layout.rs", "parse_layout"): _RAW_TYPED_CONTRACTS[("src/codestream/layout.rs", "parse_layout")],
    ("src/decode/execution.rs", "decode_layout_selected"): _LAYOUT_DECODING_CONTRACTS[("src/decode/execution.rs", "decode_layout_selected")],
    ("src/decode/api.rs", "typed_layout"): _TYPED_LAYOUT_CONTRACTS[("src/decode/api.rs", "typed_layout")],
    ("src/jp2/container.rs", "validate_selected_header"): _JPX_SOURCE_CONTRACTS[("src/jp2/container.rs", "validate_selected_header")],
    ("src/decode/output.rs", "apply_jp2_output"): _RAW_CONTAINER_COLOR_CONTRACTS[("src/decode/output.rs", "apply_jp2_output")],
}
_RAW_JPX_PUBLIC_IMAGE_MODELS = {("specs/jpx_public_images.rs", name) for name in (
    "part2_decode_jpx_selected_layout", "part2_decode_jpx_selected_source", "part2_decode_jpx_selected_file",
    "part2_decode_jpx_file_request", "part2_decode_raw_jpx_typed", "part2_decode_jpx_selected_color", "part2_decode_raw_jpx_color",
)} | {
    ("specs/jp2_container.rs", "part2_parse_container"),
    ("specs/jpx_raw_frame.rs", "part2_raw_jpx_decode_input"),
    ("specs/jpx_source.rs", "part2_decode_jpx_codestream"),
    ("specs/raw_layout.rs", "part1_parse_layout"),
    ("specs/decoder_input.rs", "part2_decoder_input_from_raw"),
    ("specs/decoder_input.rs", "part2_decode_layout_selected_value_input"),
    ("specs/decoder_input.rs", "part2_typed_layout_input"),
    ("specs/container_colors.rs", "part2_color_selection_raw"),
    ("specs/mod.rs", "part2_associated_codestream_header"),
    ("specs/mod.rs", "part2_validate_selected_header"),
    ("specs/mod.rs", "part2_apply_output_header"),
    ("specs/mod.rs", "part2_convert_associated"),
    ("specs/mod.rs", "part2_convert_associated_selected"),
    ("specs/mod.rs", "part2_decode_layout_selected"),
    ("specs/mod.rs", "part2_typed_layout"),
}
_RAW_JPX_PUBLIC_IMAGE_PROOFS = {
    *_RAW_JPX_PUBLIC_IMAGE_APIS,
    ("specs/jpx_public_images.rs", "part2_decode_jpx_selected_file_unfold"),
    ("specs/jpx_public_images.rs", "part2_decode_raw_jpx_typed_unfold"),
    ("specs/jpx_public_images.rs", "part2_decode_raw_jpx_color_unfold"),
    ("src/jp2/proof_support.rs", "raw_render_file_known"),
    ("src/jp2/proof_support.rs", "associated_header_reference_selectors"),
    ("src/jp2/proof_support.rs", "source_codestream_association_reference"),
    ("src/jp2/proof_support.rs", "source_association_parsed_reference"),
    ("src/jp2/proof_support.rs", "jpx_file_associated_header_reference"),
    ("src/jp2/proof_support.rs", "jpx_file_associated_header_reference_unfold"),
    ("src/codestream/decoder_input_proof_support.rs", "decoder_layout_input_matches_raw"),
    ("src/codestream/decoder_input_proof_support.rs", "decoder_layout_main_info_matches_raw"),
    ("src/codestream/proof_support.rs", "complete_codestream_info_known_fields"),
    ("src/decode/proof_support.rs", "associated_typed_outcome_known"),
    ("src/jp2/container.rs", "CodestreamBox::codestream_header"),
    ("src/jp2/container.rs", "CodestreamHeaderAssociation::parsed_header"),
    ("src/jp2/container.rs", "CodestreamHeaderAssociation::box_header"),
}
_RAW_JPX_PUBLIC_IMAGE_TESTS = {("src/decode/jpx_source_result_tests.rs", "actual_raw_jpx_public_" + name) for name in (
    "selects_real_nonzero_codestreams_and_complete_typed_planes",
    "preserves_tile_region_reduction_and_selected_source_limits",
    "selected_producer_retains_actual_fallback_and_associated_header_references",
    "derives_associated_palette_rgb_and_complete_alpha_output",
    "inspects_only_the_chosen_payload_after_raw_profile_and_index_admission",
    "keeps_layout_header_selection_packet_and_palette_first_errors",
)} | {("src/decode/tests.rs", "sarah_dev_355fe751f9_reduced_tile_nlt_uses_native_coordinates")}
_RAW_COMPOSITION_RENDER_ENTRY = "part2-complete-native-public-raw-composition-result"
_RAW_COMPOSITION_RENDER_APIS = {("src/jpx/render.rs", "render_jpx_composition")}
_RAW_COMPOSITION_RENDER_CONTRACTS = {
    ("src/jpx/render.rs", "render_jpx_composition"): (
        "part2_render_raw_jpx_composition", _coverage_call("crate::color::converted_image_result", r"\1"), None,
        r"input\s*@\s*,\s*" + _coverage_call("crate::options::decode_options_limits", "options"),
    ),
    ("src/jpx/render.rs", "composition_dimensions"): (
        "part2_composition_dimensions", r"\1", None,
        _coverage_call("inspection_value_view", "inspection") + r"\s*,\s*limits",
    ),
    ("src/jpx/render.rs", "render_decoded_layers"): (
        "part2_render_layers", _coverage_call("crate::color::converted_image_result", r"\1"), None,
        r"width\s*,\s*height\s*,\s*" + _coverage_call("placement_views", r"layers\s*@")
        + r"\s*,\s*maximum_decoded_bytes\s*,\s*" + _coverage_call("crate::limits::resource_work_limit", "limits"),
    ),
    ("src/jpx/render.rs", "render_inspected_frame"): _SOURCE_FRAME_CONTRACTS[("src/jpx/render.rs", "render_inspected_frame")],
    ("src/jpx/layer_decode.rs", "decode_effective_layer"): _EFFECTIVE_LAYER_CONTRACTS[("src/jpx/layer_decode.rs", "decode_effective_layer")],
}
_RAW_COMPOSITION_RENDER_MODELS = {("specs/jpx_raw_composition.rs", name) for name in (
    "part2_render_raw_jpx_composition", "part2_render_source_composition", "part2_composition_dimensions",
    "part2_composition_extent_prefix", "part2_composition_source_prefix",
)} | {
    ("specs/jp2_inspection.rs", "part2_parse_and_inspect_container"),
    ("specs/jpx_raw_frame.rs", "part2_raw_jpx_decode_input"),
    ("specs/jpx_raw_frame.rs", "part2_raw_layer_routings"),
    ("specs/jpx_raw_inspection.rs", "part2_ensure_raw_jpx"),
    ("specs/jpx_raw_inspection.rs", "part2_raw_inspection_file"),
    ("specs/jpx_raw_inspection.rs", "part2_raw_inspection_geometries"),
    ("specs/jpx_inspection.rs", "part2_inspect_jpx_file"),
    ("specs/jpx_frame.rs", "part2_render_inspected_source_frame"),
    ("specs/jpx_dispatch.rs", "part2_decode_effective_layer"),
    ("specs/mod.rs", "part2_render_layers"),
}
_RAW_COMPOSITION_RENDER_PROOFS = {
    ("specs/jpx_raw_composition.rs", "part2_render_raw_jpx_composition_unfold"),
    ("specs/jpx_raw_composition.rs", "part2_composition_extent_error"),
    ("specs/jpx_raw_composition.rs", "part2_composition_source_error"),
    ("src/jpx/proof_support.rs", "inspection_value_view"),
    ("src/jpx/proof_support.rs", "inspection_value_known"),
    ("src/jpx/proof_support.rs", "inspection_native_layers"),
    ("src/jpx/proof_support.rs", "inspected_layer_geometry"),
    ("src/jpx/proof_support.rs", "inspected_layer_geometry_known"),
    ("src/jpx/proof_support.rs", "inspection_layers_geometry_known"),
    ("src/jpx/proof_support.rs", "placement_views_push"),
    ("src/jp2/proof_support.rs", "raw_render_file_known"),
    *_RAW_COMPOSITION_RENDER_APIS,
} | {("src/jpx/inspection.rs", name) for name in (
    "JpxLayerInfo::horizontal_offset", "JpxLayerInfo::vertical_offset", "JpxLayerInfo::width", "JpxLayerInfo::height",
    "JpxInspection::layers", "JpxInspection::layer",
)}
_EFFECTIVE_LAYER_MODELS = {("specs/jpx_dispatch.rs", name) for name in (
    "part2_decode_effective_layer", "part2_layer_config_lookup", "part2_decode_compositing_layer",
    "part2_dispatch_owned_image", "part2_dispatch_opacity_result", "part2_dispatch_registration",
)}
_EFFECTIVE_LAYER_PROOFS = {("src/jp2/proof_support.rs", name) for name in (
    "source_file_layer_configs", "source_layer_routing_config", "source_layer_color_override",
    "jpx_file_layer_reference",
)}
_GENERAL_LAYER_ENTRY = "part2-complete-native-general-layer-result"
_GENERAL_LAYER_CONTRACTS = {
    ("src/jpx/layer_decode.rs", "decode_general_compositing_layer"): (
        "part2_decode_general_layer", _coverage_call("owned_layer_outcome", r"\1"), None,
        _coverage_call("jp2::jpx_file_decode_view", "file") + r"\s*,\s*"
        + _coverage_call("jp2::general_layer_config", "file", "layer") + r"\s*,\s*layer_index\s*,\s*"
        + _coverage_call("crate::options::decode_options_limits", "options"),
    ),
}
_GENERAL_LAYER_MODELS = {
    ("specs/jpx_general.rs", name) for name in (
        "part2_decode_general_layer", "part2_general_sources_prefix", "part2_general_source_step",
        "part2_general_assembled_sources_prefix", "part2_general_components_prefix", "part2_general_component_step",
        "part2_general_definitions", "part2_general_records_prefix", "part2_general_default_colors",
        "part2_general_after_assembly", "part2_general_finish",
    )
}
_GENERAL_LAYER_PROOFS = {
    ("specs/jpx_general.rs", name) for name in (
        "part2_general_sources_step", "part2_general_sources_error",
        "part2_general_assembled_sources_step", "part2_general_assembled_sources_error",
        "part2_general_components_step", "part2_general_components_error",
        "part2_general_records_step", "part2_general_records_error",
    )
} | {
    ("src/decode/proof_support.rs", "associated_typed_outcome_known"),
    ("src/jpx/proof_support.rs", "general_source_views_push"),
    ("src/jp2/proof_support.rs", "general_layer_config"),
}
_GENERAL_LAYER_HANDOFFS = (
    "let color = layer.color_group().first().unwrap_or(&file.header().color);",
    "let color_count = layer_color_count(color)?;",
    "let (image, _) = crate::decode::decode_jpx_file(file, codestream_index, options)?;",
    "width = width.min(registered_width);", "height = height.min(registered_height);",
    "crate::specs::part2_general_sources_prefix(input, config, layer_index, limits, source_index as nat)",
    "crate::specs::part2_general_components_prefix(source, config, width, height, component_index as nat, initial)",
    "crate::color::normalize_component(component, image.width(), image.height(), image.x_origin(), image.y_origin(),)",
    "u32::from(layer.horizontal_grid_size()), u32::from(layer.vertical_grid_size()), *horizontal_offset, *vertical_offset,",
    "TypedSamples::Unsigned(widen_samples(&samples)?)",
    "crate::image::typed_component_from_parts(",
    "clear_channel_definitions(&mut components);", "validate_layer_definition(record.definition, color_count)?;",
    "descriptors.push((component.info().precision, component.info().signed));",
    "crate::image::typed_image_from_components_with_origin(width, height, 0, 0, components, options.limits(),)?",
    "crate::color::convert_jp2_color(&assembled, color, options.limits())?",
    "owned_layer_from_image(&converted)?",
    "normalized_chroma_keys_for_components(values, descriptors.get(..color_count).ok_or_else(invalid_layer)?,)",
    "apply_chroma_key(&mut owned, &keys)?;",
)
_COMPONENT_PLANE_ENTRY = "part2-complete-native-component-registration-plane-result"
_COMPONENT_PLANE_CONTRACTS = {
    ("src/jpx/registration.rs", "register_samples"): (
        "part2_register_component_plane", _coverage_call("crate::color::normalized_plane_result", r"\1"), None,
        r"crate::specs::Part2PlaneRegistration\s*\{\s*source\s*:\s*source@\s*,\s*"
        r"source_width\s*,\s*source_height\s*,\s*width\s*,\s*height\s*,\s*horizontal_subsampling\s*,\s*"
        r"vertical_subsampling\s*,\s*horizontal_grid\s*,\s*vertical_grid\s*,\s*horizontal_offset\s*,\s*vertical_offset\s*,?\s*\}",
    ),
}
_SOURCE_OPACITY_CONTRACTS = {
    ("src/jpx/opacity.rs", "apply_layer_opacity"): (
        "part2_apply_source_layer_opacity", r"\1",
        _coverage_call("owned_layer_view", _coverage_call("final", "owned")),
        _coverage_call("jp2::jpx_file_decode_view", "file") + r"\s*,\s*"
        + _coverage_call("jp2::source_layer_opacity", "layer") + r"\s*,\s*"
        + _coverage_call("jp2::source_layer_geometry", "layer") + r"\s*,\s*color_codestream\s*,\s*"
        + _coverage_call("owned_layer_view", _coverage_call("old", "owned")) + r"\s*,\s*"
        r"match\s+alpha_registration\s*\{\s*None\s*=>\s*None\s*,\s*Some\s*\(\s*registration\s*\)\s*=>\s*"
        + _coverage_call("Some", _coverage_call("layer_registration_view", "registration")) + r"\s*,?\s*\}\s*,\s*"
        + _coverage_call("crate::options::decode_options_limits", "options"),
    ),
    ("src/jpx/layer_decode.rs", "decode_layer"): _JPX_LAYER_COLOR_CONTRACTS[("src/jpx/layer_decode.rs", "decode_layer")],
    ("src/jpx/layer_decode.rs", "owned_layer_from_image"): (
        "part2_owned_layer_input", _coverage_call("owned_layer_outcome", r"\1"), None,
        r"\s*,\s*".join(
            _coverage_call("crate::color::converted_image_view", "image") + rf"\s*\.{index}" for index in (0, 1, 2)
        ) + r"\s*,\s*" + _coverage_call("crate::color::converted_channel_views",
                                      _coverage_call("crate::color::converted_image_view", "image") + r"\s*\.4"),
    ),
    ("src/jpx/registration.rs", "register_layer"): _LAYER_TRAVERSAL_CONTRACTS[("src/jpx/registration.rs", "register_layer")],
    ("src/jpx/opacity.rs", "copy_registered_layer_opacity"): _LAYER_EXTERNAL_ALPHA_CONTRACTS[("src/jpx/opacity.rs", "copy_registered_layer_opacity")],
    ("src/jpx/opacity.rs", "set_layer_alpha_mode"): _LAYER_OPACITY_CONTRACTS[("src/jpx/opacity.rs", "set_layer_alpha_mode")],
    ("src/jpx/chroma.rs", "normalized_chroma_keys"): _LAYER_KEY_CONTRACTS[("src/jpx/chroma.rs", "normalized_chroma_keys")],
    ("src/jpx/chroma.rs", "apply_chroma_key_with_policy"): _LAYER_OPACITY_CONTRACTS[("src/jpx/chroma.rs", "apply_chroma_key_with_policy")],
}


def validate_normative_coverage(
    coverage: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Check the links present, without asserting exhaustive clause coverage."""
    if coverage is None:
        coverage = json.loads((VALIDATION / "normative-coverage.json").read_text())
    validate_schema(VALIDATION / "normative-coverage.schema.json", coverage)
    texts: dict[Path, str] = {}
    symbols: dict[Path, set[str]] = {}
    headers: dict[tuple[Path, str], re.Match[str] | None] = {}
    bodies: dict[tuple[Path, str], str | None] = {}
    implementation_ranges: dict[tuple[str, str, str], list[tuple[int, int, str]] | None] = {}
    file_calls: dict[Path, set[str]] = {}

    def source_text(path: Path) -> str:
        if path not in texts:
            texts[path] = path.read_text(encoding="utf-8")
        return texts[path]

    def function_header(path: Path, symbol: str) -> re.Match[str] | None:
        key = (path, symbol)
        if key not in headers:
            headers[key] = _coverage_function_header(
                source_text(path), symbol, implementation_ranges=implementation_ranges,
                module_scope=(path == (ROOT / "src/decode/output.rs").resolve()
                              and symbol == "decode_jpx_file_selected"),
            )
        return headers[key]

    def cross_file_call(
        path: Path, caller: str, callee: str, *, require_caller_body: bool,
    ) -> bool:
        if require_caller_body:
            if (path == (ROOT / "src/jpip/cache.rs").resolve()
                    and caller == "DatabinCache::insert" and callee == "jpip_final_length_consistent"):
                text = source_text(path)
                caller_body = _coverage_function_body(text, function_header(path, caller))
                helper_body = _coverage_function_body(text, function_header(path, "Databin::validate_final_length"))
                if (caller_body is not None and helper_body is not None
                        and "databin.validate_final_length(&fragment,incoming_end)?" in "".join(caller_body.split())
                        and "crate::refinement::jpip_final_length_consistent(final_length,new_final)" in "".join(helper_body.split())):
                    return True
            def through_style_producer(
                current_path: Path, current_caller: str, visited: set[tuple[Path, str]],
            ) -> bool:
                if same_file_call(current_path, current_caller, callee, distinct_file=True):
                    return True
                owner = current_caller.rsplit("::", 1)[0] if "::" in current_caller else None
                for (relay_path, relay), binding in _COMPONENT_PRODUCER_RELAYS.items():
                    if owner is None or not relay.startswith(owner + "::"):
                        continue
                    relay_short = relay.rsplit("::", 1)[-1]
                    resolved = (ROOT / relay_path).resolve()
                    key = (resolved, relay)
                    if key in visited or relay_short == callee or not same_file_call(
                        current_path, current_caller, relay_short, distinct_file=True,
                    ):
                        continue
                    header = function_header(resolved, relay)
                    if header is None:
                        continue
                    text = source_text(resolved)
                    start = text.rfind("#[cfg_attr(verus_keep_ghost, verus_spec(", 0, header.start())
                    contract = text[start:header.start()] if start >= 0 else ""
                    model, projection, final_state, arguments = binding
                    result_term = (projection if final_state is None else
                                   r"\(\s*" + projection + r"\s*,\s*" + final_state + r"\s*\)")
                    match = re.search(
                        r"\bverus_spec\(\s*(\w+)\s*=>\s*ensures\s+" + result_term
                        + r"\s*==\s*crate::specs::(?P<model>" + re.escape(model) + r")\s*\(",
                        contract,
                    )
                    signature = text[header.start():text.find("{", header.end())]
                    mutable = set(re.findall(r"\b(\w+)\s*:\s*&\s*mut\b", signature))
                    if re.search(r"&\s*mut\s+self\b", signature):
                        mutable.add("self")
                    framed = set(re.findall(
                        r"\bfinal\(\s*(\w+)\s*\)", match.group() if match is not None else ""))
                    if (re.search(r"\brequires\b", contract) is None and mutable == framed
                            and _coverage_result_arguments(contract, match, model, arguments)
                            and through_style_producer(resolved, relay, visited | {key})):
                        return True
                return False
            return through_style_producer(path, caller, {(path, caller)})
        text = source_text(path)
        if re.fullmatch(r"\w+", callee) is None:
            return re.search(rf"\b{re.escape(callee)}\s*\(", text) is not None
        if path not in file_calls:
            file_calls[path] = set(re.findall(r"\b(\w+)\s*\(", text))
        return callee in file_calls[path]

    def same_file_call(
        path: Path, caller: str, callee: str, *, distinct_file: bool = False,
    ) -> bool:
        same_name = caller.rsplit("::", 1)[-1] == callee
        if same_name and not distinct_file:
            return False
        key = (path, caller)
        if key not in bodies:
            bodies[key] = _coverage_function_body(source_text(path), function_header(path, caller))
        body = bodies[key]
        if (callee == "read_tile_header" and caller == "Parser::read_tile_part"
                and path.relative_to(ROOT).as_posix() == "src/codestream/tiles.rs"):
            for field in ("completed_mct", "completed_mcc"):
                binding = "_" + field
                if (body is None or re.search(r"\b" + field + r"\s*:\s*" + binding + r"\s*,", body) is None
                        or len(re.findall(r"\b" + binding + r"\b", body)) != 1):
                    return False
        admission = _COMPONENT_SEGMENT_ADMISSION_CALLERS.get(
            (path.relative_to(ROOT).as_posix(), caller),
        ) if callee == "record_component_segment" else None
        if admission is not None:
            receiver, components, owner = admission
            return body is not None and all(re.search(
                _coverage_call(
                    receiver + "." + callee, "segment", components,
                    "MalformedKind::" + kind, r"&\s*mut\s*" + owner + slots + r"\s*,?",
                ), body,
            ) is not None for kind, slots in (
                ("InvalidCodingStyle", "coc_segments"),
                ("InvalidQuantization", "qcc_segments"),
            ))
        if (callee == "classify_codestream_profile"
                and path.relative_to(ROOT).as_posix() == "src/codestream/layout.rs"
                and caller == "Parser::parse_layout"):
            produced = re.search(
                r"\blet\s+codestream_profile\s*=\s*" + _coverage_call(
                    callee, "r_siz", "extended_capabilities", "profile", "corresponding_profile",
                    r"&\s*component_coding_styles", r"&\s*roi_shifts", r"&\s*tile_part_payloads",
                    r"image_size\.components",
                    _coverage_call("roi_seen.iter") + r"\s*\.\s*" + _coverage_call("any", _RAW_ROI_PREDICATE)
                    + r"\s*,?",
                ) + r"\s*\?\s*;", body,
            ) if body is not None else None
            return (produced is not None and re.search(
                r"\bprofile\s*:\s*codestream_profile\s*,", body[produced.end():],
            ) is not None)
        if (callee == "tile_part_main_metadata"
                and path.relative_to(ROOT).as_posix() == "src/codestream/layout.rs"
                and caller == "Parser::parse_layout"):
            admission = (
                r"\blet\s+tile_part\s*=\s*" + _coverage_call("parser.read_sot", "tile_count")
                + r"\s*\?\s*;\s*#\[\s*cfg\s*\(\s*verus_keep_ghost\s*\)\s*\]\s*proof!\s*\{\s*"
                + _coverage_call("assert", r"tile_parts\s*>\s*0") + r"\s*;\s*\}\s*"
                r"let\s*\(\s*main_packet_lengths\s*,\s*packed_packet_headers\s*\)\s*=\s*"
                r"parser\s*\.\s*" + _coverage_call(
                    callee, "tile_part", r"tile_parts\s*-\s*1",
                    r"&\s*part2_extensions\.tile_part_lengths", "plm_seen",
                    r"&\s*plm_groups", r"&\s*ppm_frames", "ppm_fragments", r"main_header\s*,?",
                ) + r"\s*\?\s*;"
            )
            handoff = _coverage_call(
                "parser.read_tile_part", "tile_part",
                r"\(\s*inherited_default_style\s*,\s*inherited_default_quantization\s*\)",
                "inherited_component_styles", "inherited_component_quantizations",
                "inherited_roi_shifts", "inherited_progression_changes",
                "inherited_mct_parameters", "inherited_part2_extensions",
                r"image_size\.components", "main_packet_lengths", r"packed_packet_headers\s*,?",
            )
            selected = re.search(admission, body) if body is not None else None
            consumed = re.search(handoff, body) if body is not None else None
            return selected is not None and consumed is not None and selected.end() < consumed.start()
        if (callee == "finish_tile_part_traversal"
                and path.relative_to(ROOT).as_posix() == "src/codestream/layout.rs"
                and caller == "Parser::parse_layout"):
            return body is not None and re.search(
                r"\bEOC\s*=>\s*\{\s*" + _coverage_call(
                    "parser." + callee, "tile_parts", "plm_seen",
                    _coverage_call("plm_groups.len"), "ppm_fragments",
                    _coverage_call("ppm_frames.len"),
                    _coverage_call("part2_extensions.tile_part_lengths.len") + r"\s*,?",
                ) + r"\s*\?\s*;\s*break\s*;\s*\}", body,
            ) is not None
        if (callee == "select_inherited_tile_configuration"
                and path.relative_to(ROOT).as_posix() == "src/codestream/layout.rs"
                and caller == "Parser::parse_layout"):
            return body is not None and re.search(_coverage_call(
                "parser." + callee, "tile_index", r"&\s*roi_shifts", r"&\s*coding_style",
                r"&\s*quantization", r"&\s*component_coding_styles",
                r"&\s*tile_roi_shifts", r"&\s*tile_coding_styles", r"&\s*tile_quantizations",
                r"&\s*tile_component_style_parts", r"&\s*tile_part_payloads\s*,?",
            ), body) is not None
        if (callee == "commit_persistent_tile_configuration"
                and path.relative_to(ROOT).as_posix() == "src/codestream/layout.rs"
                and caller == "Parser::parse_layout"):
            return body is not None and re.search(_coverage_call(
                "parser." + callee, r"tile_part\.start", "tile_index",
                _coverage_call("tile_part_payloads.len"), "previous_roi_shifts", r"&\s*payload",
                r"&\s*mut\s*tile_roi_shifts", r"&\s*mut\s*tile_coding_styles",
                r"&\s*mut\s*tile_quantizations", r"&\s*mut\s*tile_component_style_parts",
                r"&\s*mut\s*tile_component_quantizations", r"&\s*mut\s*tile_progression_changes\s*,?",
            ), body) is not None
        prefix = r"(?<![\w.])" if same_name else r"\b"
        return body is not None and re.search(rf"{prefix}{re.escape(callee)}\s*\(", body) is not None

    ids: set[str] = set()
    contract_functions: set[tuple[str, str]] = set()
    for entry in coverage["requirements"]:
        if entry["id"] == _JPIP_PHASE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPIP_PHASE_CONTRACTS):
                raise ValueError("automatic phase Results require all complete native error/state contracts")
            model_source = source_text((ROOT / "specs/jpip_phases.rs").resolve())
            for name, fragments in {
                "part2_jpip_ordinal_cell_phase": ("before.is_some()", ")), before)", "(Ok(()), Some(sequence))"),
                "part2_jpip_order_phase": (
                    "part1_progression_iterator_next(iterator)",
                    "match step.0 { Err(error) => (Err(error), step.1, ordinals, order)",
                    "Ok(None) => (Ok(()), step.1, ordinals, order)", "remaining == 0",
                    "coordinate.layer as nat >= ordinals[execution as int].len()",
                    "ordinals[execution as int][coordinate.layer as int].is_some()",
                    "let order = order.push((coordinate, execution))", "ordinal == u64::MAX",
                    "(Err(part2_jpip_range_overflow(0)), step.1, ordinals, order)",
                ),
                "part2_jpip_precinct_phase": (
                    "execution as nat >= plan.precincts.len()", "(Err(part2_jpip_range_overflow(0)), plan)",
                    "part1_jpip_precinct_packet(plan.precincts[execution as int], template,",
                    "prefix.subrange(start as int, prefix.len() as int)", "precincts: plan.precincts.update(execution as int, step.1), ..plan",
                ),
                "part2_jpip_emit_packet_phase": (
                    "packet.3 && packet.5 < available", "MalformedKind::MissingRequiredStructure)), before)",
                    "(Ok(()), before + bytes)", "part2_jpip_empty_packet_bytes(sop, eph, packet.4)",
                ),
                "part2_jpip_emit_packets_phase": (
                    "Err(error) => (Err(error), step.1)",
                    "part2_jpip_emit_packets_phase(part, available, packet + 1, step.1)",
                ),
                "part2_jpip_emit_part_patch": ("(Err(part2_jpip_range_overflow(0)), before)",
                    "part2_jpip_write_u32(before, (start as nat + 6) as usize, (before.len() - start as nat) as u32)"),
                "part2_jpip_emit_part_phase": ("before + part.0", "Err(error) => (Err(error), packets.1)",
                    "part2_jpip_emit_part_patch(packets.1, before.len() as usize)"),
            }.items():
                body = _coverage_spec_function_body(model_source, name)
                if {"path": "specs/jpip_phases.rs", "symbol": name} not in entry["spec_refs"] \
                        or body is None or any("".join(item.split()) not in "".join(body.split()) for item in fragments):
                    raise ValueError("automatic phase Results require exact partial-error state and ordered native effects")
        if entry["id"] == _JPIP_BYTE_RESULT_ENTRY:
            contracts = set(_JPIP_BYTE_RESULT_CONTRACTS)
            consumer = ("src/jpip/progression.rs", "DatabinCache::build_automatic_snapshot")
            law = ("specs/jpip_byte_writes.rs", "part2_jpip_write_u32_short_saturated_window")
            for field, required in (
                ("implementation_refs", contracts | {consumer, ("src/jpip/mapping.rs", "DatabinCache::derive_precinct_map")}),
                ("contract_refs", contracts),
                ("spec_refs", {("specs/jpip_byte_writes.rs", name) for name in _JPIP_BYTE_RESULT_MODELS}),
                ("proof_refs", contracts | {consumer, law}),
                ("test_refs", _JPIP_BYTE_RESULT_TESTS),
            ):
                if not required.issubset({(ref["path"], ref["symbol"]) for ref in entry[field]}):
                    if field == "implementation_refs":
                        raise ValueError("linked function is not used by claimed implementation: JPIP word/template Results")
                    raise ValueError("JPIP word/template Results require complete producers, consumers, models and regressions")
            source = source_text((ROOT / "specs/jpip_byte_writes.rs").resolve())
            for name, fragments in _JPIP_BYTE_RESULT_MODELS.items():
                body = _coverage_spec_function_body(source, name)
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in fragments):
                    raise ValueError("JPIP word/template Results require exact partial-error frames, ordered patches and limits")
            snapshot_source = source_text((ROOT / consumer[0]).resolve())
            snapshot = _coverage_function_body(
                snapshot_source, _coverage_function_header(snapshot_source, consumer[1]))
            for fragment in (
                "part2_jpip_transition_template(normalized_main@,",
                "tile@.map_values(|header: Vec<u8>| header@)), limits) == Ok(template@)",
                "emit_automatic_tile_part(&mut bytes, part, available_layers)?",
            ):
                if snapshot is None or "".join(fragment.split()) not in "".join(snapshot.split()):
                    raise ValueError("JPIP word/template Results require the actual snapshot byte-frame cutpoints")
            phase_source = source_text((ROOT / "src/jpip/automatic_phases.rs").resolve())
            emitter = _coverage_function_body(
                phase_source, _coverage_function_header(phase_source, "emit_automatic_tile_part"))
            for fragment in (
                "let ghost before_empty = bytes@",
                "(Ok(()), bytes@) == crate::specs::part2_jpip_append_empty_packet("
                "before_empty, part.sop, part.eph, packet.ordinal)",
                "let ghost before_psot = bytes@",
                "(Ok(()), bytes@) == crate::specs::part2_jpip_write_u32("
                "before_psot, length_position, tile_length)",
            ):
                if emitter is None or "".join(fragment.split()) not in "".join(emitter.split()):
                    raise ValueError("JPIP word/template Results require the actual snapshot byte-frame cutpoints")
        if entry["id"] == _JPIP_AUTOMATIC_INPUT_ENTRY:
            contracts = set(_JPIP_AUTOMATIC_INPUT_CONTRACTS) | {
                ("src/jpip/progression.rs", "DatabinCache::automatic_headers"),
                ("src/jpip/automatic_headers.rs", "normalize_main_header"),
                ("src/jpip/automatic_headers.rs", "normalize_automatic_tile_headers"),
                ("src/jpip/cache.rs", "DatabinCache::databin_view"),
            }
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != contracts:
                raise ValueError("automatic header/partition inputs require every complete actual Result contract")
            for field, required in (
                ("implementation_refs", contracts | {
                    ("src/jpip/progression.rs", "DatabinCache::build_automatic_snapshot"),
                    ("src/jpip/mapping.rs", "DatabinCache::derive_precinct_map"),
                }),
                ("proof_refs", {
                    ("src/jpip/progression_proof_support.rs", name) for name in (
                        "jpip_automatic_headers_view", "jpip_automatic_headers_outcome",
                        "jpip_automatic_headers_witness", "jpip_automatic_headers_first_error",
                        "jpip_automatic_packet_view",
                        "jpip_automatic_packets_view", "jpip_automatic_tile_part_view",
                        "jpip_automatic_partition_outcome",
                    )
                }),
                ("test_refs", {
                    ("src/jpip/normalization_result_tests.rs",
                     "automatic_cardinality_preserves_first_siz_and_geometry_before_tile_limit_errors"),
                    *(("src/jpip/tests.rs", name) for name in (
                        "automatic_header_inputs_preserve_cache_siz_and_reservation_error_order",
                        "automatic_header_inputs_derive_exact_fields_and_recover_after_managed_refusal",
                        "automatic_tile_partition_derives_packet_fields_missing_and_exact_boundary_errors",
                    )),
                }),
            ):
                if not required.issubset({(ref["path"], ref["symbol"]) for ref in entry[field]}):
                    if field == "implementation_refs":
                        raise ValueError("automatic header/partition inputs not used by claimed implementation: actual consumers missing")
                    raise ValueError("automatic header/partition inputs require actual consumers, complete views and regressions")
            models = {
                "specs/jpip_normalization.rs": {
                    "part2_jpip_ceil_div": ("divisor == 0", "value as int + divisor as int - 1 > u64::MAX as int"),
                    "part2_jpip_siz_payload": (
                        "payload.len() < 36", "part2_jpip_read_u32(payload, 2)",
                        "part2_jpip_read_u32(payload, 6)", "part2_jpip_read_u32(payload, 18)",
                        "part2_jpip_read_u32(payload, 22)", "part2_jpip_read_u32(payload, 26)",
                        "part2_jpip_read_u32(payload, 30)", "part2_jpip_read_u16(payload, 34)",
                        "components == 0", "width == 0", "height == 0", "x <= tx", "y <= ty",
                        "components > crate::limits::resource_component_limit(limits)",
                        "count > crate::limits::resource_tile_limit(limits) as nat",
                    ),
                    "part2_jpip_siz_scan": ("remaining == 0", "part2_jpip_marker_segment(input, position)",
                        "marker == 0xff51", "part2_jpip_siz_payload(", "(remaining - 1) as usize"),
                    "part2_jpip_siz_cardinality": ("input.len() < 2", "input[0] != 0xff", "input[1] != 0x4f"),
                    "part2_jpip_automatic_headers_finish": (
                        "if events.len() == 0 { Some(result) } else { None }",
                    ),
                    "part2_jpip_header_capacity": ("events.len() == 0", "actual == site && count == elements"),
                    "part2_jpip_automatic_raw_tiles": ("part2_jpip_cache_view(cache, (2u64,",
                        "tile + 1, output.push(bytes)"),
                    "part2_jpip_automatic_first_tiles": ("index > u16::MAX as nat",
                        "part2_jpip_normalize_automatic_tile_headers(tiles[index as int], index as u16)",
                        "headers.len() == 0", "index + 1, output.push(headers[0])"),
                    "part2_jpip_automatic_headers_normalized": (
                        "part2_jpip_header_capacity(events, 1, tiles.len() as usize)",
                        "Err(crate::DecodeError::AllocationFailed), events.drop_first()",
                        "part2_jpip_automatic_first_tiles(tiles, 0, Seq::empty())",
                        "Ok((main, normalized, count, components))",
                    ),
                    "part2_jpip_automatic_headers_bins": ("Err(error) => part2_jpip_automatic_headers_finish(Err(error), events)",
                        "part2_jpip_normalize_main_header(main, calls)",
                        "Some(Err(error)) => part2_jpip_automatic_headers_finish(Err(error), events.drop_first())",
                        "part2_jpip_automatic_headers_normalized("),
                    "part2_jpip_automatic_headers": ("part2_jpip_cache_view(cache, (6u64,",
                        "part2_jpip_siz_cardinality(main, &cache.0)", "count > usize::MAX as u64",
                        "part2_jpip_header_capacity(events, 0, count as usize)",
                        "part2_jpip_automatic_raw_tiles(cache, stream, count, 0, Seq::empty())"),
                    "part2_jpip_automatic_headers_result": (
                        "exists|events: Seq<Part2JpipAutomaticHeaderEvent>|",
                        "part2_jpip_automatic_headers(cache, stream, events) == Some(result)",
                    ),
                },
                "specs/jpip_progressive.rs": {
                    "part2_jpip_partition_bytes": ("packets[end as int].1", "None => Ok(None)",
                        "consumed as nat + (bytes.len() as u64) as nat", "consumed != target",
                        "part2_jpip_cache_error(consumed, crate::MalformedKind::InvalidPacketLength)"),
                    "part2_jpip_partition_end": ("part + 1 == count", "match transition.2",
                        "packets_in_part > usize::MAX as u64", "match transition.3",
                        "part2_jpip_partition_bytes(packets, target, start as nat, 0)"),
                    "part2_jpip_partition_parts": ("start as nat != packets.len()", "Ok(None) => Ok(None)",
                        "start > end || end as nat > packets.len()", "packets.subrange(start as int, end as int)",
                        "state.coding_style.sop_markers, state.coding_style.eph_markers"),
                    "part2_jpip_partition_automatic_tiles": ("headers.len() != states.len()",
                        "headers.len() != transitions.len()", "headers.len() == 0",
                        "part2_jpip_partition_parts(headers, states, transitions, packets, 0, 0, Seq::empty())"),
                },
            }
            for relative, recipes in models.items():
                source = source_text((ROOT / relative).resolve())
                for name, fragments in recipes.items():
                    if {"path": relative, "symbol": name} not in entry["spec_refs"]:
                        raise ValueError("automatic header/partition inputs require every stage model")
                    body = _coverage_spec_function_body(source, name)
                    if body is None or any("".join(fragment.split()) not in "".join(body.split()) for fragment in fragments):
                        raise ValueError("automatic header/partition inputs require exact native error/request/byte models")
            views = source_text((ROOT / "src/jpip/progression_proof_support.rs").resolve())
            for name, fragments in {
                "jpip_automatic_headers_view": (
                    "value.main@", "value.tiles@.map_values", "value.tile_count", "value.components"),
                "jpip_automatic_packet_view": (
                    "databin_id_view(value.databin)", "jpip_parsed_packet_value(value.bytes)",
                    "value.next_offset", "value.required", "value.ordinal", "value.layer"),
                "jpip_automatic_tile_part_view": (
                    "value.header@", "value.packets@.map_values", "jpip_automatic_packet_view(&packet)",
                    "value.sop", "value.eph"),
            }.items():
                body = _coverage_spec_function_body(views, name)
                if body is None or any("".join(fragment.split()) not in "".join(body.split()) for fragment in fragments):
                    raise ValueError("automatic header/partition inputs require every returned field projection")
        if entry["id"] == "part9-packet-reframing":
            required = {
                "proof_refs": {
                    ("src/jpip/progression.rs", "DatabinCache::build_automatic_snapshot"),
                    ("src/decode/planning.rs", "ProgressionTilePlan::grid"),
                    ("src/decode/planning.rs", "ProgressionTilePlan::precincts"),
                    ("src/decode/planning.rs", "ProgressionTilePlan::precincts_mut"),
                    ("src/jpip/progression_proof_support.rs", "jpip_filter_projection"),
                    ("src/jpip/progression_proof_support.rs", "jpip_parsed_packet_value"),
                    ("src/jpip/progression_proof_support.rs", "jpip_parsed_packet_row"),
                    ("src/jpip/progression_proof_support.rs", "jpip_parsed_packet_matrix"),
                    ("src/jpip/progression_proof_support.rs", "jpip_parsed_packet_matrix_update"),
                    ("src/jpip/progression_proof_support.rs", "jpip_parsed_packet_row_update"),
                },
                "spec_refs": {
                    ("specs/jpip_progressive.rs", "part2_jpip_ordinal_matrix_write"),
                    ("specs/jpip_progressive.rs", "part2_jpip_packet_matrix_write"),
                },
                "test_refs": {
                    ("src/jpip/tests.rs", "automatic_mapping_decodes_incomplete_precinct_quality_prefixes"),
                    ("src/jpip/tests.rs", "automatic_managed_allocation_refusals_preserve_state_and_recover_exact_images"),
                },
            }
            if any(not refs.issubset({(ref["path"], ref["symbol"]) for ref in entry[field]})
                   for field, refs in required.items()):
                raise ValueError("ordinal scratch frame requires its actual proof, model and controls")
            source = source_text((ROOT / "src/jpip/progression.rs").resolve())
            body = _coverage_function_body(
                source, _coverage_function_header(source, "DatabinCache::build_automatic_snapshot"),
            )
            phase_source = source_text((ROOT / "src/jpip/automatic_phases.rs").resolve())
            phase = _coverage_function_body(
                phase_source, _coverage_function_header(phase_source, "build_automatic_order"))
            cell = _coverage_function_body(
                phase_source, _coverage_function_header(phase_source, "write_automatic_ordinal"))
            if body is None or "build_automatic_order(&plan, &mut iterator, &mut ordinals, &mut order, limits)?" not in body:
                raise ValueError("ordinal scratch frame requires its actual non-owning phase consumer")
            if cell is None or any("".join(item.split()) not in "".join(cell.split()) for item in (
                "if slot.is_some() { return Err(DecodeError::malformed(0, MalformedKind::InvalidProgressionOrderChange, )); }",
                "*slot = Some(sequence)",
            )):
                raise ValueError("ordinal scratch frame requires its exact checked cell error/update")
            native_fragments = (
                "let ghost before_ordinals = ordinals@.map_values(|row: Vec<Option<u16>>| row@)",
                "let layer_slot = match ordinals.get_mut(execution) { "
                "Some(layers) => layers.get_mut(usize::from(coordinate.layer)), None => None, }",
                "assert(*layer_slot == before_ordinals[execution as int][coordinate.layer as int])",
                "match write_automatic_ordinal(layer_slot, sequence)",
                "assert(crate::specs::part2_jpip_ordinal_matrix_write(before_ordinals, "
                "ordinals@.map_values(|row: Vec<Option<u16>>| row@), execution, coordinate.layer, sequence))",
                "order.push((coordinate, execution))",
            )
            compact = "".join(body.split()) if body is not None else ""
            phase_compact = "".join(phase.split()) if phase is not None else ""
            positions = [phase_compact.find("".join(fragment.split())) for fragment in native_fragments]
            if any(position < 0 for position in positions) or positions != sorted(positions):
                raise ValueError("ordinal scratch frame requires the original lookup/error/duplicate/write/order handoff")
            model = source_text((ROOT / "specs/jpip_progressive.rs").resolve())
            body = _coverage_spec_function_body(model, "part2_jpip_ordinal_matrix_write")
            model_fragments = (
                "(execution as nat) < before.len()",
                "(layer as nat) < before[execution as int].len()",
                "before[execution as int][layer as int].is_none()",
                "after == before.update(execution as int, "
                "before[execution as int].update(layer as int, Some(sequence)))",
            )
            if body is None or any("".join(fragment.split()) not in "".join(body.split())
                                   for fragment in model_fragments):
                raise ValueError("ordinal scratch frame requires exact bounds, old empty slot and complete matrix update")
            packet_fragments = (
                "let ghost before_native = parsed@",
                "let ghost before_parsed = jpip_parsed_packet_matrix(parsed@)",
                "*(match parsed.get_mut(execution) { "
                "Some(layers) => layers.get_mut(usize::from(coordinate.layer)), None => None, })"
                ".ok_or_else(|| { DecodeError::malformed(0, MalformedKind::ArithmeticOverflow) })?"
                " = Some(copy_bytes(packet_slice))",
                "assert(crate::specs::part2_jpip_packet_matrix_write(before_parsed, "
                "jpip_parsed_packet_matrix(parsed@), execution, coordinate.layer, packet_slice@))",
            )
            positions = [compact.find("".join(fragment.split())) for fragment in packet_fragments]
            if any(position < 0 for position in positions) or positions != sorted(positions):
                raise ValueError("packet scratch frame requires actual bytes and the original assignment ordering")
            packet_model = _coverage_spec_function_body(model, "part2_jpip_packet_matrix_write")
            if packet_model is None or any("".join(fragment.split()) not in "".join(packet_model.split())
                                          for fragment in (
                                              "(execution as nat) < before.len()",
                                              "(layer as nat) < before[execution as int].len()",
                                              "after == before.update(execution as int, "
                                              "before[execution as int].update(layer as int, Some(bytes)))",
                                          )):
                raise ValueError("packet scratch frame requires complete bounds and byte matrix update")
            projections = source_text((ROOT / "src/jpip/progression_proof_support.rs").resolve())
            for name, fragments in {
                "jpip_parsed_packet_value": ("None => None", "Some(bytes) => Some(bytes@)"),
                "jpip_parsed_packet_row": ("value@.map_values(", "jpip_parsed_packet_value(cell)"),
                "jpip_parsed_packet_matrix": ("value.map_values(", "jpip_parsed_packet_row(row)"),
            }.items():
                projection = _coverage_spec_function_body(projections, name)
                if projection is None or any("".join(fragment.split()) not in "".join(projection.split())
                                             for fragment in fragments):
                    raise ValueError("packet scratch frame requires complete native byte projections")
            planning_path = (ROOT / "src/decode/planning.rs").resolve()
            planning = source_text(planning_path)
            for symbol, clauses, returned in (
                ("ProgressionTilePlan::grid", (
                    "ensures crate::packet::packet_grid_view(result) == progression_plan_view(self).grid",
                ), "&self.grid"),
                ("ProgressionTilePlan::precincts", (
                    "ensures super::planning_precincts_view(result@) == progression_plan_view(self).precincts",
                ), "&self.precincts"),
                ("ProgressionTilePlan::precincts_mut", (
                    "ensures super::planning_precincts_view(result@) == progression_plan_view(old(self)).precincts",
                    "progression_plan_view(final(self)) == (crate::specs::Part2ProgressionTilePlan { "
                    "precincts: super::planning_precincts_view(final(result)@), "
                    "..progression_plan_view(old(self)) })",
                ), "&mut self.precincts"),
            ):
                header = function_header(planning_path, symbol)
                signature = planning.find("fn", header.start(), header.end()) if header else -1
                attrs = planning[planning.rfind("#[cfg_attr", 0, signature):signature] if signature >= 0 else ""
                body = _coverage_function_body(planning, header)
                if ("verus_spec(" not in attrs or re.search(r"\b(?:requires|assume|admit|external_body)\b", attrs)
                        or any("".join(clause.split()) not in "".join(attrs.split()) for clause in clauses)
                        or body is None or "".join(returned.split()) not in "".join(body.split())):
                    raise ValueError("automatic inputs require complete checked plan getter and future-slice frames")
            input_fragments = (
                "let tile_parts_iterator = layout.tile_parts.iter().filter(",
                "let tile_parts: Vec<_> = tile_parts_iterator.collect()",
                "super::jpip_filter_projection(source.remaining(), keep, project, predicate)",
                "assert(tile_parts@.map_values(project) == "
                "crate::codestream::tile_parts_owned_view(layout.tile_parts@).filter(predicate))",
            )
            if any("".join(fragment.split()) not in compact for fragment in input_fragments):
                raise ValueError("automatic inputs require the actual selected-tile order and complete payload projection")
        if entry["id"] in _RAW_RECOVERY_PUBLIC_ENTRIES:
            reconstructed = entry["id"] == _RECONSTRUCTED_RECOVERY_ENTRY
            contracts = _RECONSTRUCTED_RECOVERY_CONTRACTS if reconstructed else _RAW_RECOVERY_CONTRACTS
            relations = _RECONSTRUCTED_RECOVERY_RELATIONS if reconstructed else _RAW_RECOVERY_RELATIONS
            expected = set(contracts) | set(relations)
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != expected:
                raise ValueError("raw recovery requires all actual preflight/state/copy/admission/report/public contracts")
            lib = source_text((ROOT / "src/lib.rs").resolve())
            if not re.search(
                r"pub\s+use\s+recovery::\{[^}]*\b"
                + re.escape(_RAW_RECOVERY_PUBLIC_ENTRIES[entry["id"]]) + r"\b[^}]*\}", lib,
            ):
                raise ValueError("raw recovery requires its actual public root export")
            if reconstructed:
                if not expected.issubset({(ref["path"], ref["symbol"]) for ref in entry["implementation_refs"]}):
                    raise ValueError("reconstructed recovery not used by claimed implementation")
                required = {
                    ("specs/raw_recovery.rs", name) for name in (
                        "raw_reconstructed_recovery_result", "raw_reconstructed_recovery_result_body",
                        "raw_reconstructed_recovery_reserved_response", "raw_reconstructed_recovery_finish",
                        "raw_recovery_report", "raw_repair_response", "raw_recovery_framing",
                    )
                } | {("specs/raw_decode.rs", "part2_decode_raw_reconstructed_codestream")}
                if not required.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}):
                    raise ValueError("reconstructed recovery requires actual framing, reservation, reconstruction and report models")
                model = source_text((ROOT / "specs/raw_recovery.rs").resolve())
                for name, fragments in {
                    "raw_reconstructed_recovery_result_body": (
                        "match raw_recovery_framing(input, limits)",
                        "match raw_recovery_admit(input.len() as usize, frame.1, limits)",
                        "part2_decode_raw_reconstructed_codestream(input, limits)",
                        "raw_reconstructed_recovery_reserved_response(input, limits, frame, false)",
                        "raw_reconstructed_recovery_reserved_response(input, limits, frame, true)",
                    ),
                    "raw_reconstructed_recovery_reserved_response": (
                        "match raw_repair_response(input, reserved)",
                        "part2_decode_raw_reconstructed_codestream(bytes, limits)",
                    ),
                    "raw_reconstructed_recovery_finish": (
                        "Err(error) => Err(error)",
                        "raw_recovery_report(original, frame, (image.0, image.1, image.2, image.3))",
                        "Ok(report) => Ok((image, report))",
                    ),
                }.items():
                    body = _coverage_spec_function_body(model, name)
                    if body is None or any("".join(fragment.split()) not in "".join(body.split())
                                           for fragment in fragments):
                        raise ValueError("reconstructed recovery requires complete raw reconstruction and report composition")
        if entry["id"] == "part9-ordered-main-header-storage-result":
            main = ("src/jpip/automatic_headers.rs", "normalize_main_header")
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != {main}:
                raise ValueError("ordered main-header storage requires its complete actual Result contract")
            for field, required in (
                ("implementation_refs", {main,
                    ("src/jpip/progression.rs", "DatabinCache::build_automatic_snapshot"),
                    ("src/jpip/progression.rs", "DatabinCache::automatic_headers")}),
                ("proof_refs", {main,
                    ("src/jpip/automatic_headers.rs", "main_header_result_witness"),
                    ("src/jpip/automatic_headers.rs", "main_header_storage_events_are_ordered")}),
                ("test_refs", {
                    ("src/jpip/normalization_result_tests.rs",
                     "automatic_main_header_refusal_preserves_input_and_exact_recovery"),
                    ("src/jpip/normalization_result_tests.rs",
                     "automatic_main_header_requests_preserve_validation_and_reservation_error_order")}),
            ):
                if not required.issubset({(ref["path"], ref["symbol"]) for ref in entry[field]}):
                    if field == "implementation_refs":
                        raise ValueError("ordered main-header storage not used by claimed implementation")
                    raise ValueError("ordered main-header storage requires actual consumers and request/error controls")
            model = source_text((ROOT / "specs/jpip_normalization.rs").resolve())
            fragments = {
                "part2_jpip_storage_event": (
                    "events.len() == 0", "events[0].0 != operation", "events[0].1 != length",
                    "events[0].2 != requested", "Some(events[0].3)",
                ),
                "part2_jpip_main_header_finish": (
                    "if events.len() == 0 { Some(result) } else { None }",
                ),
                "part2_jpip_normalize_main_header": (
                    "input.len() < 2 || input[0] != 0xff || input[1] != 0x4f",
                    "part2_jpip_storage_event(events, 0, 0, 2)",
                    "part2_jpip_storage_event(events.drop_first(), 1, 0, 2)",
                    "Err(crate::DecodeError::AllocationFailed), events.drop_first()",
                    "seq![0xffu8, 0x4fu8], events.drop_first().drop_first()",
                ),
                "part2_jpip_main_header_scan": (
                    "part2_jpip_marker_segment(input, position)",
                    "Err(error) => part2_jpip_main_header_finish(Err(error), events)",
                    "marker == 0xff90 || marker == 0xff93 || marker == 0xffd9",
                    "part9_reframed_marker_removed(marker as nat, false)",
                    "part2_jpip_storage_event(events, 1, output.len() as usize, bytes.len() as usize)",
                    "Err(crate::DecodeError::AllocationFailed), events.drop_first()",
                    "output + bytes, events.drop_first()",
                ),
                "part2_jpip_main_header_result": (
                    "exists|events: Seq<Part2JpipStorageEvent>|",
                    "part2_jpip_normalize_main_header(input, events) == Some(result)",
                ),
            }
            required_models = {("specs/jpip_normalization.rs", name) for name in fragments}
            if not required_models.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}):
                raise ValueError("ordered main-header storage requires every request/result model")
            for name, required in fragments.items():
                body = _coverage_spec_function_body(model, name)
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("ordered main-header storage requires exact ordered request/error models")
        if entry["id"] == _JPIP_TRANSITION_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPIP_TRANSITION_CONTRACTS) - _JPIP_TRANSITION_APIS:
                raise ValueError("whole raw JPIP transitions require complete actual parser/word/marker/count/cache consumers")
            for field, required in (
                ("implementation_refs", set(_JPIP_TRANSITION_CONTRACTS) | _JPIP_TRANSITION_CALLERS),
                ("spec_refs", _JPIP_TRANSITION_MODELS), ("proof_refs", _JPIP_TRANSITION_PROOFS),
                ("test_refs", _JPIP_TRANSITION_TESTS),
            ):
                if not required.issubset({(ref["path"], ref["symbol"]) for ref in entry[field]}):
                    raise ValueError("whole raw JPIP transitions linked function is not used by claimed implementation: actual raw/header/PLT/cache/need/getter bridge missing")
            path = (ROOT / "src/jpip/mapping.rs").resolve()
            text = source_text(path)
            for name, clause in _JPIP_TRANSITION_GETTERS.items():
                header = function_header(path, name)
                signature = text.find("fn", header.start(), header.end()) if header else -1
                attrs = text[text.rfind("#[cfg_attr", 0, signature):signature] if signature >= 0 else ""
                if "ensures" + "".join(clause.split()) + "," not in "".join(attrs.split()) or re.search(r"\brequires\b", attrs):
                    raise ValueError("whole raw JPIP transitions require complete stored transition/report/need getters")
            for relative, name, required in (
                ("src/jpip/automatic_headers.rs", "normalize_automatic_tile_headers", (
                    "parse_tile_part_transitions(input, tile)?", "u8::try_from(transitions.len())",
                    "normalize_tile_header(transition.header_bytes(), tile, index, count)?", "output.push(header)",
                )),
                ("src/jpip/automatic_headers.rs", "normalize_tile_header", (
                    "source.starts_with(&[0xff, 0x90])", "marker_segment(source, 0)?",
                    "marker != 0xff90 || end != 12", "u8::try_from(index)", "header.push(count)",
                    "remaining_markers = source.len()", "remaining_markers -= 1",
                    "source.get(position..position.saturating_add(2)) == Some(&[0xff, 0x93])",
                    "marker_segment(source, position)?", "jpip_reframed_marker_removed(marker, true)",
                    "if position != source.len() { return Err", "header.extend_from_slice(&[0xff, 0x93])",
                )),
                ("src/jpip/byte_io.rs", "read_u16_be", (".get(position..position.saturating_add(2))", ".first()", ".get(1)", "u16::from(high) << 8")),
                ("src/jpip/byte_io.rs", "read_u32_be", (".get(position..position.saturating_add(4))", ".first()", ".get(3)", "u32::from(first) << 24")),
                ("src/jpip/automatic_headers.rs", "marker_segment", ("read_u16_be(input, position)?",
                    "matches!(marker, 0xff4f | 0xff93 | 0xffd9)", "length < 2", "read_u16_be(input, length_position)?", "end > input.len()")),
                ("src/jpip/mapping.rs", "count_plt_packets", ("payload.is_empty()", "let mut position = 1_usize",
                    "continuation = byte & 0x80 != 0", "count.checked_add(1)", "if continuation")),
                ("src/jpip/mapping.rs", "parse_tile_part_transitions", (
                    "!input.starts_with(&[0xff, 0x90])", "remaining_markers = input.len()", "remaining_parts = input.len()",
                    "remaining_headers = input.len()", "marker_segment(input, position)?", "count_plt_packets(",
                    "header: copy_bytes(input)", "marker != 0xff90 || sot_end.checked_sub(position) != Some(12)",
                    "read_u16_be(input, position + 4)?", "tile != expected_tile", "read_u32_be(input, position + 6)?",
                    "u16::from(index) != next_plt", "next_plt.checked_add(1)", "!found_sod",
                    "tile_part_length == 0 && position < input.len()", "Some(declared.checked_sub(header_length).ok_or_else(",
                    "copy_bytes(input.get(part_start..position)", "invariant_except_break",
                    "part2_jpip_transition_parts(input@, expected_tile, position, remaining_parts, jpip_transitions_view(&transitions))",
                )),
                ("src/jpip/mapping.rs", "DatabinCache::tile_part_transitions", (
                    "DatabinId::new(2, codestream, u64::from(tile))?", "!self.is_complete(id)",
                    "self.complete_databin_missing(id)", "self.databin_view(id)?.into_bytes()",
                    "parse_tile_part_transitions(&bytes, tile)?", "jpip_tile_transition_sufficient(",
                    "transition.packet_count().is_none() && transition.data_length().is_none()", "preceding_packets_known = false",
                    "(u64::from(tile) << 8) | u64::from(transition.tile_part())", "if needs.is_empty()",
                )),
            ):
                target = (ROOT / relative).resolve()
                body = _coverage_function_body(source_text(target), function_header(target, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw JPIP transitions require original word/marker/PLT/SOT/SOD/cache/need handoffs")
            model = source_text((ROOT / "specs/jpip_transitions.rs").resolve())
            for name, required in {
                "part2_jpip_read_u16": ("position as nat + 2 > input.len()", "position as nat + 2 > usize::MAX as nat"),
                "part2_jpip_read_u32": ("position as nat + 4 > input.len()", "position as nat + 4 > usize::MAX as nat"),
                "part2_jpip_marker_segment": ("part2_jpip_read_u16(input, position)", "marker == 0xff4f || marker == 0xff93 || marker == 0xffd9",
                    "length < 2", "end > usize::MAX as nat", "end > input.len()"),
                "part2_jpip_plt_scan": ("payload[position as int] & 0x80 != 0", "count == u64::MAX", "if continuation", "position + 1"),
                "part2_jpip_transition_scan": ("remaining == 0", "if indexed", "payload.len() == 0 || payload[0] as u16 != next_plt",
                    "indexed && next_plt == u16::MAX", "part2_jpip_plt_count(payload)", "total > u64::MAX as nat",
                    "marker == 0xff61 || marker == 0xff64", "(remaining - 1) as usize"),
                "part2_jpip_transition_parts": ("marker != 0xff90 || end as nat != position as nat + 12",
                    "actual_tile != tile", "part2_jpip_read_u32", "!scan.4", "length == 0 && (scan.0 as nat) < input.len()",
                    "length != 0 && (length as nat) < header_length", "let data = if length == 0 { None }",
                    "input.subrange(position as int, scan.0 as int)",
                    "transitions.push(transition)"),
                "part2_jpip_parse_transitions": ("input.len() >= 2 && input[0] == 0xff && input[1] == 0x90",
                    "part2_jpip_transition_scan(input, 0, input.len() as usize, false, false, None, 0)",
                    "Ok(seq![(tile, 0u8, scan.2, None, scan.1, input)])"),
                "part2_jpip_transition_needs": ("jpip_tile_transition_sufficient(transition.4, preceding_known, transition.3.is_some())",
                    "((tile as u64) << 8) | transition.1 as u64", "preceding_known && (transition.2.is_some() || transition.3.is_some())"),
                "part2_jpip_transition_report": ("(2u64, crate::jpip::DatabinClass::TileHeader, stream, tile as u64)",
                    "!part2_jpip_cache_complete(cache, id)", "part2_jpip_complete_missing(cache, id)",
                    "part2_jpip_cache_view(cache, id)", "part2_jpip_parse_transitions(bytes, tile)",
                    "part2_jpip_transition_needs(transitions, 0, true, Seq::empty(), tile)",
                    "if needs.len() == 0", "crate::jpip::JpipAvailability::Partial"),
            }.items():
                body = _coverage_spec_function_body(model, name)
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw JPIP transitions require complete native extent/PLT/header/error/prefix/report models")
            model = source_text((ROOT / "specs/jpip_normalization.rs").resolve())
            for name, required in {
                "part2_jpip_normalized_header_scan": (
                    "remaining == 0", "position as nat != source.len()", "end != source.len()",
                    "part2_jpip_marker_segment(source, position)", "part9_reframed_marker_removed(marker as nat, true)",
                    "output + source.subrange(position as int, end as int)", "output + seq![0xffu8, 0x93u8]",
                ),
                "part2_jpip_normalized_header_after_start": (
                    "index > u8::MAX as usize", "((tile >> 8) & 0xff) as u8", "(tile & 0xff) as u8",
                    "index as u8, count", "part2_jpip_normalized_header_scan(source, start, source.len() as usize,",
                ),
                "part2_jpip_normalize_tile_header": (
                    "source.len() >= 2 && source[0] == 0xff && source[1] == 0x90",
                    "part2_jpip_marker_segment(source, 0)", "marker != 0xff90 || end != 12",
                    "part2_jpip_normalized_header_after_start(source, tile, index, count, end)",
                    "part2_jpip_normalized_header_after_start(source, tile, index, count, 0)",
                ),
                "part2_jpip_normalized_header_entries": (
                    "part2_jpip_normalize_tile_header(entries[position as int].5, tile,",
                    "position as usize, entries.len() as u8", "position + 1, output.push(header)",
                ),
                "part2_jpip_normalize_automatic_tile_headers": (
                    "part2_jpip_parse_transitions(input, tile)", "Err(error) => Err(error)",
                    "entries.len() > u8::MAX as nat",
                    "part2_jpip_normalized_header_entries(entries, tile, 0, Seq::empty())",
                ),
            }.items():
                body = _coverage_spec_function_body(model, name)
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw JPIP transitions require complete native normalization Result models")
        if entry["id"] == _JPIP_PROGRESSIVE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPIP_PROGRESSIVE_CONTRACTS) - _JPIP_PROGRESSIVE_APIS:
                raise ValueError("whole caller JPIP progressive requires complete actual availability/transcode/full-selected consumers")
            for field, required in (
                ("implementation_refs", set(_JPIP_PROGRESSIVE_CONTRACTS)),
                ("spec_refs", _JPIP_PROGRESSIVE_MODELS), ("proof_refs", _JPIP_PROGRESSIVE_PROOFS),
                ("test_refs", _JPIP_PROGRESSIVE_TESTS),
            ):
                if not required.issubset({(ref["path"], ref["symbol"]) for ref in entry[field]}):
                    raise ValueError("whole caller JPIP progressive linked function is not used by claimed implementation: actual header/layer/transcode/image/state/owner bridge missing")
            path = (ROOT / "src/jpip/progression.rs").resolve()
            text = source_text(path)
            for name, clause in _JPIP_PROGRESSIVE_BODY_CLAUSES.items():
                if not _coverage_verified_body_clause(text, function_header(path, name), name, clause):
                    raise ValueError("whole caller JPIP progressive requires exact checked owned constructor/impl clauses")
            for name, clause in _JPIP_PROGRESSIVE_GETTERS.items():
                header = function_header(path, name)
                signature = text.find("fn", header.start(), header.end()) if header else -1
                attrs = text[text.rfind("#[cfg_attr", 0, signature):signature] if signature >= 0 else ""
                if "ensures" + "".join(clause.split()) + "," not in "".join(attrs.split()) or re.search(r"\brequires\b", attrs):
                    raise ValueError("whole caller JPIP progressive requires complete stored update fields and image values")
                owner = {"JpipProgressiveUpdate::image": "result == jpip_progressive_image_borrow(self)",
                         "JpipProgressiveUpdate::into_image": "result == *jpip_progressive_image_owner(&self)"}.get(name)
                if owner is not None and "".join(owner.split()) not in "".join(attrs.split()):
                    raise ValueError("whole caller JPIP progressive requires original optional image borrow/move owner")
            for name in ("JpipProgressiveDecoder::update", "JpipProgressiveDecoder::update_selected", "JpipProgressiveDecoder::update_inner"):
                header = function_header(path, name)
                signature = text.find("fn", header.start(), header.end()) if header else -1
                attrs = text[text.rfind("#[cfg_attr", 0, signature):signature] if signature >= 0 else ""
                if "".join("jpip_progressive_plan_owner(final(self)) == jpip_progressive_plan_owner(old(self))".split()) not in "".join(attrs.split()):
                    raise ValueError("whole caller JPIP progressive requires original native plan frame on every Result")
            for relative, name, required in (
                ("src/jpip/progression.rs", "JpipProgressiveDecoder::update", ("self.update_inner(cache, options, None)",)),
                ("src/jpip/progression.rs", "JpipProgressiveDecoder::update_selected", ("self.update_inner(cache, options, Some(selection))",)),
                ("src/jpip/progression.rs", "JpipProgressiveDecoder::update_inner", (
                    "let previous_layers = self.decoded_layers", "cache.progressive_availability(&self.plan)?",
                    "jpip_progressive_update_valid(", "jpip_quality_prefix_available(", "available_layers <= previous_layers",
                    "cache.transcode_precinct_codestream(&self.plan, available_layers)?",
                    "crate::decode_codestream_selected(view.as_ref(), options, selection)?",
                    "crate::decode_codestream(view.as_ref(), options)?", "self.decoded_layers = available_layers",
                    "image: None", "image: Some(image)", "JpipProgressiveStatus::QualityAdvanced",
                )),
                ("src/jpip/ranges.rs", "DatabinCache::progressive_availability", (
                    "self.append_complete_databin_requirement(plan.main_header, &mut header_report)?",
                    "self.append_complete_databin_requirement(plan.tile_header, &mut header_report)?",
                    "!header_report.missing.is_empty()", "while layer < plan.layer_ends.len()", ".get(start..end)",
                    "|packet: &JpipPrecinctPacket| packet.range", "self.availability(&ranges)?",
                    "u16::try_from(layer)", "start = end", "layer += 1",
                    "part2_jpip_progressive_layers(cache, packets, ends, layer as nat, start)",
                )),
            ):
                target = (ROOT / relative).resolve()
                body = _coverage_function_body(source_text(target), function_header(target, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole caller JPIP progressive requires original header/layer/iterator/transcode/full-selected/state handoffs")
                if name == "DatabinCache::progressive_availability" and "".join(body.split()).count("u16::try_from(layer)") != 2:
                    raise ValueError("whole caller JPIP progressive requires both original physical layer-count narrowing checks")
            model = source_text((ROOT / "specs/jpip_progressive.rs").resolve())
            for name, required in {
                "part2_jpip_progressive_layers": ("layer > u16::MAX as nat", "start > end || end as nat > packets.len()",
                    "packets.subrange(start as int, end as int)", "part2_jpip_cache_availability(cache, ranges)",
                    "Ok((layer as u16, report.3))", "part2_jpip_progressive_layers(cache, packets, ends, layer + 1, end)"),
                "part2_jpip_progressive_availability": ("part2_jpip_append_complete_requirement(cache, plan.0",
                    "part2_jpip_append_complete_requirement(cache, plan.1, main.1)", "Ok((0, tile.1.3))",
                    "part2_jpip_progressive_layers(cache, plan.2, plan.3, 0, 0)"),
                "part2_jpip_progressive_update": ("planned = decoder.0.3.len() as u16",
                    "part2_jpip_progressive_availability(cache, decoder.0)", "valid_jpip_progressive_update",
                    "available <= previous", "part2_jpip_transcode(cache, decoder.0, available)",
                    "part2_decode_raw_codestream(", "crate::options::decode_options_limits(options), selection",
                    "Err(error) => (Err(error), decoder)", "previous, available, missing, Some(image)",
                    "(decoder.0, available)"),
            }.items():
                body = _coverage_spec_function_body(model, name)
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole caller JPIP progressive requires complete physical layer/full-selected-image/final-state models")
                if name == "part2_jpip_progressive_layers" and "".join(body.split()).count("iflayer>u16::MAXasnat") != 2:
                    raise ValueError("whole caller JPIP progressive requires both complete narrowing error models")
        if entry["id"] == _JPIP_TRANSCODE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPIP_TRANSCODE_CONTRACTS) - _JPIP_TRANSCODE_APIS:
                raise ValueError("whole JPIP transcode requires complete actual availability/header/packet consumers")
            for field, required in (
                ("implementation_refs", set(_JPIP_TRANSCODE_CONTRACTS)),
                ("spec_refs", _JPIP_TRANSCODE_MODELS), ("proof_refs", _JPIP_TRANSCODE_PROOFS),
                ("test_refs", _JPIP_TRANSCODE_TESTS),
            ):
                if not required.issubset({(ref["path"], ref["symbol"]) for ref in entry[field]}):
                    raise ValueError("whole JPIP transcode linked function is not used by claimed implementation: actual header/availability/raw-validation/owner bridge missing")
            for (relative, name), clause in _JPIP_TRANSCODE_FRAMES.items():
                path = (ROOT / relative).resolve()
                text, header = source_text(path), function_header(path, name)
                signature = text.find("fn", header.start(), header.end()) if header else -1
                attrs = text[text.rfind("#[cfg_attr", 0, signature):signature] if signature >= 0 else ""
                if "ensures" + "".join(clause.split()) + "," not in "".join(attrs.split()) or re.search(r"\brequires\b", attrs):
                    raise ValueError("whole JPIP transcode requires complete stored values and mutable first-error frames")
                owner = {"JpipPrecinctTranscode::availability": "result == jpip_transcode_availability_owner(self)",
                         "JpipPrecinctTranscode::into_codestream": "result == *jpip_transcode_byte_owner(&self)"}.get(name)
                if owner is not None and "".join(owner.split()) not in "".join(attrs.split()):
                    raise ValueError("whole JPIP transcode requires original availability borrow and optional byte move owners")
            for relative, name, required in (
                ("src/jpip/precinct.rs", "DatabinCache::transcode_precinct_codestream", (
                    "plan.packet_end_for_layers(layers)?", "self.precinct_availability(plan, packet_end)?",
                    "!availability.is_available()", "self.databin_view(plan.main_header)?.into_bytes()",
                    "self.databin_view(plan.tile_header)?.into_bytes()", "validate_and_patch_main_header(&mut main_header, layers)?",
                    "validate_and_patch_tile_header(&mut tile_header, layers)?", ".get(..packet_end)",
                    "self.read_packet_ranges(selected_packets)?", ".get_mut(6..10)", ".copy_from_slice(&tile_part_bytes)",
                    "jpip_reconstruction_length(", "contracted_total != total as u128", "total as u64 > self.limits.maximum_input_bytes()",
                    "bytes.extend_from_slice(&main_header)", "bytes.extend_from_slice(&tile_header)",
                    "bytes.extend_from_slice(&packet_bytes)", "bytes.extend_from_slice(&EOC)",
                    "validate_precinct_codestream(&bytes, layers, &self.limits)?", "Some(JpipByteView { bytes })",
                )),
                ("src/jpip/precinct.rs", "patch_cod_layers", (
                    "start > header.len()", "while position < header.len()", "marker == 0xff93",
                    "stop_at_sod && position + 2 == header.len()", "marker == 0xff4f || marker == 0xffd9",
                    "segment_length < 2", "segment_end <= position || segment_end > header.len()",
                    "marker == 0xff52", "segment_length < 7", "u8::try_from((layers >> 8) & 0xff)",
                    "u8::try_from(layers & 0xff)", ".get_mut(layer_start..layer_end)", ".copy_from_slice(&bytes)",
                    "position = segment_end", "part2_jpip_patch_cod_loop(header@, position, layers, stop_at_sod)",
                )),
                ("src/jpip/ranges.rs", "DatabinCache::precinct_availability", (
                    ".get(..packet_end)", "packets.iter().map(", "|packet: &JpipPrecinctPacket| packet.range",
                    "self.availability(&ranges)?", "self.append_complete_databin_requirement(plan.main_header, &mut report)?",
                    "self.append_complete_databin_requirement(plan.tile_header, &mut report)?", "report.missing.is_empty()",
                )),
                ("src/jpip/ranges.rs", "DatabinCache::append_complete_databin_requirement", (
                    "self.status(id)", "status.final_length()", ".checked_add(status.contiguous_prefix())",
                    "final_length == 0", "self.availability(&[JpipDatabinRange::new(id, 0, final_length)?])?",
                    ".checked_add(header_report.required_bytes)", ".checked_add(header_report.available_bytes)",
                    "report.missing.push(header_report.missing[missing_index])",
                )),
                ("src/jpip/precinct.rs", "validate_precinct_codestream", (
                    "crate::codestream::parse_layout(bytes, limits)?", "jpip_precinct_layout_fields(&layout)",
                    "layout.info.image_size.tile_count()? != 1", "layout.tile_parts.len() != 1",
                    "layout.info.coding_style.layers != layers", "layout.tile_parts[0].coding_style.progression_order",
                    "layout.info.progression_changes.is_present()", "layout.tile_parts[0].progression_changes.is_present()",
                    "layout.tile_parts[0].packet_lengths.is_present()", "layout.tile_parts[0].packed_packet_headers.is_present()",
                )),
            ):
                path = (ROOT / relative).resolve()
                body = _coverage_function_body(source_text(path), function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole JPIP transcode requires original header/length/iterator/availability/raw-validation handoffs")
            model = source_text((ROOT / "specs/jpip_transcode.rs").resolve())
            for name, required in {
                "part2_jpip_append_complete_requirement": ("part2_jpip_cache_status(cache, id)", "report.3.push((id, 0, None))",
                    "available > u64::MAX as nat", "required > u64::MAX as nat", "Err(part2_jpip_range_overflow(0)), committed"),
                "part2_jpip_precinct_availability": ("end as nat > plan.2.len()", "part2_jpip_cache_availability(cache, ranges)",
                    "part2_jpip_append_complete_requirement(cache, plan.0, report)", "part2_jpip_append_complete_requirement(cache, plan.1, main.1)"),
                "part2_jpip_patch_cod_loop": ("position as nat + 2 > header.len()", "marker == 0xff93", "length < 7",
                    "header.update(position as int + 6", ".update(position as int + 7", "part2_jpip_patch_cod_loop(patched, end as usize, layers, stop)"),
                "part2_jpip_validate_precinct_raw": ("part1_parse_layout(bytes, limits)", "part2_selection_tile_count(layout.0.image_size.geometry)",
                    "layout.0.coding_style.layers != layers", "tile.coding_style.progression_order", "tile.packet_lengths.source", "tile.packed_packet_headers.source"),
                "part2_jpip_transcode_bytes": ("length > usize::MAX as nat || length > u32::MAX as nat", "tile.update(6",
                    ".update(9", "total > usize::MAX as nat", "resource_input_byte_limit", "seq![0xffu8, 0xd9u8]",
                    "part2_jpip_validate_precinct(bytes, layers, &cache.0)", "Ok(()) => Ok(bytes)"),
                "part2_jpip_transcode_payload": ("part2_jpip_cache_view(cache, plan.0)", "part2_jpip_cache_view(cache, plan.1)",
                    "part2_jpip_patch_main(main, layers)", "part2_jpip_patch_tile(tile, layers)",
                    "part2_jpip_read_packets(cache, plan.2.subrange(0, end as int))"),
                "part2_jpip_transcode": ("part2_jpip_plan_packet_end(plan, layers)", "part2_jpip_precinct_availability(cache, plan, end)",
                    "availability.0 != crate::jpip::JpipAvailability::Available", "part2_jpip_transcode_payload(cache, plan, end, layers)",
                    "Ok((layers, availability, Some(bytes)))"),
            }.items():
                body = _coverage_spec_function_body(model, name)
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole JPIP transcode requires complete mutable-header/partial-report/byte/raw-parse models")
        if entry["id"] == _JPIP_PLANNED_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPIP_PLANNED_CONTRACTS) - _JPIP_PLANNED_APIS:
                raise ValueError("whole planned JPIP packets require complete actual availability/byte consumers")
            for field, required in (
                ("implementation_refs", set(_JPIP_PLANNED_CONTRACTS)),
                ("spec_refs", _JPIP_PLANNED_MODELS), ("proof_refs", _JPIP_PLANNED_PROOFS),
                ("test_refs", _JPIP_PLANNED_TESTS),
            ):
                if not required.issubset({(ref["path"], ref["symbol"]) for ref in entry[field]}):
                    raise ValueError("whole planned JPIP packets linked function is not used by claimed implementation: actual owned/selection/iterator/availability/byte/getter/test bridge missing")
            path = (ROOT / "src/jpip/precinct.rs").resolve()
            text = source_text(path)
            for name, clause in _JPIP_PLANNED_BODY_CLAUSES.items():
                if not _coverage_verified_body_clause(text, function_header(path, name), name, clause):
                    raise ValueError("whole planned JPIP packets require exact checked owned constructor/impl clauses without premises")
            for name, clause in _JPIP_PLANNED_GETTERS.items():
                header = function_header(path, name)
                signature = text.find("fn", header.start(), header.end()) if header else -1
                attrs = text[text.rfind("#[cfg_attr", 0, signature):signature] if signature >= 0 else ""
                if "ensures" + "".join(clause.split()) + "," not in "".join(attrs.split()) or re.search(r"\brequires\b", attrs):
                    raise ValueError("whole planned JPIP packets require complete stored getter values")
                owner = {"JpipPrecinctPackets::availability": "result == jpip_planned_availability_owner(self)",
                         "JpipPrecinctPackets::into_packets": "result == *jpip_planned_packet_owner(&self)"}.get(name)
                if owner is not None and "".join(owner.split()) not in "".join(attrs.split()):
                    raise ValueError("whole planned JPIP packets require original borrow/move ownership frames")
            for name, required in {
                "JpipPrecinctPacket::new": ("databin.class(), DatabinClass::Precinct", "JpipDatabinRange::new(databin, offset, length)?", "layer,"),
                "JpipPrecinctCodestreamPlan::new": (
                    "layers == 0 || layers > limits.maximum_layers()", "main_header.class(), DatabinClass::MainHeader",
                    "main_header.in_class() != 0", "tile_header.class(), DatabinClass::TileHeader",
                    "main_header.codestream() != tile_header.codestream()", "packets.is_empty()",
                    "packets.len() as u64 > limits.maximum_packets()", "packets[packet_index].layer == layer",
                    "packet.range.databin.codestream() != main_header.codestream()", "total_bytes.checked_add(packet.range.length)",
                    "total_bytes > limits.maximum_input_bytes()", "packet_index == layer_start",
                    "layer_ends.push(packet_index)", "packet_index != packets.len()", "packets,", "layer_ends,",
                    "part2_jpip_plan_layers(main, tile, entries", "part2_jpip_plan_layer_packets(",
                ),
                "JpipPrecinctCodestreamPlan::packet_end_for_layers": ("layers == 0 || layers > self.layers()",
                    "self.layer_ends.get(usize::from(layers - 1))", "Some(end) => Ok(*end)"),
                "DatabinCache::reconstruct_precinct_packets": (
                    "plan.packet_end_for_layers(layers)?", ".get(..packet_end)", "selected_packets.iter().map(",
                    "|packet: &JpipPrecinctPacket| packet.range", ".collect()", "self.availability(&ranges)?",
                    "availability.is_available()", "self.read_packet_ranges(selected_packets)?",
                    "layers,", "availability,", "packets,", "ranges@.map_values",
                ),
            }.items():
                body = _coverage_function_body(text, function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole planned JPIP packets require original owned/layer/error/selection/iterator/cache handoffs")
            model = source_text((ROOT / "specs/jpip_planned_packets.rs").resolve())
            for name, required in {
                "part2_jpip_packet_new": ("id.1 != crate::jpip::DatabinClass::Precinct", "part2_jpip_range_new(id, offset, length)"),
                "part2_jpip_plan_layer_packets": ("packets[position as int].1 != layer", "packet.0.0.2 != main.2",
                    "next > u64::MAX as nat", "next > input_limit as nat", "position + 1"),
                "part2_jpip_plan_layers": ("position as nat != packets.len()", "next.0 == position",
                    "Err(part2_jpip_plan_invalid(layer as u64))", "ends.push(next.0)"),
                "part2_jpip_plan_new": ("resource_layer_limit", "main.3 != 0", "main.2 != tile.2",
                    "packets.len() == 0", "resource_packet_limit", "part2_jpip_plan_layers"),
                "part2_jpip_plan_packet_end": ("layers > plan.3.len() as u16", "index >= plan.3.len()", "Ok(plan.3[index as int])"),
                "part2_jpip_planned_packets": ("part2_jpip_plan_packet_end(plan, layers)", "end as nat > plan.2.len()",
                    "plan.2.subrange(0, end as int)", "selected.map_values", "part2_jpip_cache_availability(cache, ranges)",
                    "availability.0 != crate::jpip::JpipAvailability::Available", "part2_jpip_read_packets(cache, selected)",
                    "Ok((layers, availability, Some(bytes)))"),
            }.items():
                body = _coverage_spec_function_body(model, name)
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole planned JPIP packets require complete owned/layer/physical-selection/availability/byte models")
        if entry["id"] == _JPIP_RANGE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPIP_RANGE_CONTRACTS) - _JPIP_RANGE_APIS:
                raise ValueError("whole raw JPIP ranges require complete actual missing/packet-byte consumer contracts")
            for field, required in (
                ("implementation_refs", set(_JPIP_RANGE_CONTRACTS) | _JPIP_RANGE_CALLERS),
                ("spec_refs", _JPIP_RANGE_MODELS), ("proof_refs", _JPIP_RANGE_PROOFS), ("test_refs", _JPIP_RANGE_TESTS),
            ):
                if not required.issubset({(ref["path"], ref["symbol"]) for ref in entry[field]}):
                    raise ValueError("whole raw JPIP ranges linked function is not used by claimed implementation: actual range/interval/work/byte/getter/caller/test bridge missing")
            path = (ROOT / "src/jpip/ranges.rs").resolve()
            text = source_text(path)
            for name, clause in _JPIP_RANGE_BODY_CLAUSES.items():
                if not _coverage_verified_body_clause(text, function_header(path, name), name, clause):
                    raise ValueError("whole raw JPIP ranges require exact checked constructor/impl body clauses without premises")
            for name, clause in _JPIP_RANGE_GETTERS.items():
                header = function_header(path, name)
                signature = text.find("fn", header.start(), header.end()) if header else -1
                attrs = text[text.rfind("#[cfg_attr", 0, signature):signature] if signature >= 0 else ""
                if "ensures" + "".join(clause.split()) + "," not in "".join(attrs.split()) or re.search(r"\brequires\b", attrs):
                    raise ValueError("whole raw JPIP ranges require complete stored getter fields without premises")
            for name, required in {
                "DatabinCache::availability": (
                    "ranges.len() as u64 > self.limits.maximum_packets()", "requested.offset.checked_add(requested.length)",
                    "requested_end > self.limits.maximum_input_bytes()", "required_bytes.checked_add(requested.length)",
                    "required_bytes > self.limits.maximum_input_bytes()", "self.find_databin_index(requested.databin)",
                    "work.checked_add(1)", "work > self.limits.maximum_work_units()",
                    "fragment.end() <= cursor", "fragment.offset >= requested_end", "fragment.offset > cursor",
                    "fragment.offset.min(requested_end)", "cursor = fragment.end().min(requested_end)",
                    "Some(requested_end - cursor)", "missing[missing_index].length.unwrap_or(0)",
                    "required_bytes.checked_sub(missing_bytes)", "jpip_available_bytes(required_bytes, missing_bytes)",
                    "jpip_range_complete(available_bytes, required_bytes)", "required_bytes,", "available_bytes,", "missing,",
                    "part2_jpip_availability_remaining(cache, requests, range_index as nat",
                    "scan_expected == Ok((cursor, work, jpip_missing_views(&missing)))",
                    "part2_jpip_missing_total(final_missing, 0, 0)",
                ),
                "DatabinCache::complete_databin_missing": (
                    "self.status(id)", "offset: status.contiguous_prefix()", "status.final_length().map(",
                    "jpip_missing_length(", "offset: 0", "length: None",
                ),
                "DatabinCache::read_packet_ranges": (
                    "total.checked_add(packets[packet_index].range.length)", "total > self.limits.maximum_input_bytes()",
                    "usize::try_from(total)", "self.find_databin_index(range.databin)", "range.offset.checked_add(range.length)",
                    "fragment.end() <= cursor", "fragment.offset > cursor", "fragment.end().min(end)",
                    "usize::try_from(cursor - fragment.offset)", "copy_end.checked_sub(fragment.offset)",
                    "fragment.bytes.get(local_start..local_end)", "output.extend_from_slice", "cursor = copy_end",
                    "cursor != end", "part2_jpip_packet_remaining(cache, entries, packet_index as nat, output@)",
                    "previous_output + fragment.bytes@.subrange(local_start as int, local_end as int)",
                ),
                "append_missing_ranges": ("output.push(input[index])", "original + incoming.subrange(0, index as int)",
                    "jpip_missing_views(final(output)) == jpip_missing_views(old(output))"),
            }.items():
                header = function_header(path, name)
                body = _coverage_function_body(text, header)
                signature = text.find("fn", header.start(), header.end()) if header else -1
                attrs = text[text.rfind("#[cfg_attr", 0, signature):signature] if signature >= 0 else ""
                actual = "".join((attrs + (body or "")).split())
                if body is None or any("".join(item.split()) not in actual for item in required):
                    raise ValueError("whole raw JPIP ranges require original ordered range/work/missing/slice/append handoffs")
            model = source_text((ROOT / "specs/jpip_ranges.rs").resolve())
            for name, required in {
                "part2_jpip_range_new": ("length == 0", "offset as nat + length as nat > u64::MAX as nat"),
                "part2_jpip_complete_missing": ("part2_jpip_cache_status(cache, id)", "seq![(id, 0, None)]", "part9_missing_length"),
                "part2_jpip_missing_total": ("next > u64::MAX as nat", "part2_jpip_missing_total(missing, position + 1, next as u64)"),
                "part2_jpip_availability_finish": ("total > required", "part9_available_bytes", "complete_jpip_range", "required, available, missing"),
                "part2_jpip_availability_fragments": ("position >= fragments.len() || cursor >= end", "next_work > u64::MAX as nat",
                    "next_work > work_limit as nat", "fragment_end <= cursor", "fragment.0 >= end", "missing.push((requested.0, cursor",
                    "next_cursor, next_work as u64, next_missing, work_limit)"),
                "part2_jpip_availability_request": ("end > u64::MAX as nat", "end > input_limit as nat",
                    "next_required > u64::MAX as nat", "next_required > input_limit as nat", "part2_jpip_find_databin",
                    "missing.push((requested.0, requested.1, Some(requested.2)))", "part2_jpip_availability_fragments"),
                "part2_jpip_availability_remaining": ("part2_jpip_availability_finish(required, missing)", "part2_jpip_availability_request",
                    "part2_jpip_availability_remaining(cache, ranges, position + 1, next.0, next.1, next.2)"),
                "part2_jpip_cache_availability": ("resource_packet_limit", "part2_jpip_availability_remaining(cache, ranges, 0, 0, 0, Seq::empty())"),
                "part2_jpip_packet_total": ("packets[position as int].0.2 as nat", "next > u64::MAX as nat"),
                "part2_jpip_packet_fragments": ("cursor != end", "fragment_end <= cursor", "fragment.0 > cursor",
                    "start > usize::MAX as nat", "copy_end < fragment.0", "local_end > usize::MAX as nat",
                    "start > local_end || local_end > fragment.1.len()", "output + fragment.1.subrange"),
                "part2_jpip_packet_remaining": ("part2_jpip_find_databin", "index as nat >= cache.1.len()", "end > u64::MAX as nat",
                    "part2_jpip_packet_fragments", "part2_jpip_packet_remaining(cache, packets, position + 1, bytes)"),
                "part2_jpip_read_packets": ("part2_jpip_packet_total", "resource_input_byte_limit", "total as nat > usize::MAX as nat",
                    "part2_jpip_packet_remaining(cache, packets, 0, Seq::empty())"),
            }.items():
                body = _coverage_spec_function_body(model, name)
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw JPIP ranges require complete native-order interval/work/first-error/byte models")
        if entry["id"] == _JPIP_RESPONSE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPIP_RESPONSE_CONTRACTS) - _JPIP_RESPONSE_APIS:
                raise ValueError("whole raw JPIP response requires complete actual parser/cache mutation consumer contracts")
            for field, required in (
                ("implementation_refs", set(_JPIP_RESPONSE_CONTRACTS)), ("spec_refs", _JPIP_RESPONSE_MODELS),
                ("proof_refs", _JPIP_RESPONSE_PROOFS), ("test_refs", _JPIP_RESPONSE_TESTS),
            ):
                if not required.issubset({(ref["path"], ref["symbol"]) for ref in entry[field]}):
                    raise ValueError("whole raw JPIP response linked function is not used by claimed implementation: actual raw/cache/summary/error/test bridge missing")
            path = (ROOT / "src/jpip/message.rs").resolve()
            text = source_text(path)
            body = _coverage_function_body(text, function_header(path, "ingest_jpip_response"))
            required = (
                "JpipMessageParser::new(cache.limits)", "let mut position = 0_usize", "let mut messages = 0_u64",
                "parser.parse(&input[position..])?", "consumed == 0",
                "JpipFragment::from_message(header, body, &cache.limits)?", "cache.insert(fragment)?",
                "messages.checked_add(1)", "position.checked_add(consumed)", "response_end != input.len()",
                "end_of_response_reason: Some(end.reason_code)", "next_position <= position || next_position > input.len()",
                "position = next_position", "end_of_response_reason: None",
                "part2_jpip_response_remaining(input@, jpip_cache_view(cache)",
                "jpip_parser_context(&parser), *jpip_parser_limits(&parser), position, messages)",
                "assert(data == (Ok(messages), jpip_cache_view(cache)))",
            )
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                raise ValueError("whole raw JPIP response requires original raw/suffix/fragment/commit/count/EOR/advance handoffs")
            for name, (field, index) in _JPIP_RESPONSE_GETTERS.items():
                header = function_header(path, name)
                getter = _coverage_function_body(text, header)
                signature = text.find("fn", header.start(), header.end()) if header else -1
                attrs = text[text.rfind("#[cfg_attr", 0, signature):signature] if signature >= 0 else ""
                expected = f"ensures result == jpip_response_summary_view(*self).{index},"
                if (getter is None or field not in getter or "".join(expected.split()) not in "".join(attrs.split())
                        or re.search(r"\brequires\b", attrs)):
                    raise ValueError("whole raw JPIP response requires complete stored summary/getter fields without premises")
            model = source_text((ROOT / "specs/jpip_response.rs").resolve())
            for name, required in {
                "part2_jpip_response_data": (
                    "part2_jpip_fragment_from_message(header, body, &cache.0)", "part2_jpip_cache_insert(cache, fragment)",
                    "Err(error) => (Err(error), inserted.1)", "messages == u64::MAX",
                    "crate::MalformedKind::ArithmeticOverflow", "Ok((messages + 1) as u64), inserted.1",
                ),
                "part2_jpip_response_remaining": (
                    "position as nat >= input.len()", "(Ok((messages, None)), cache)",
                    "part2_parse_jpip_message(input.subrange(position as int, input.len() as int), context, &parser_limits)",
                    "Err(error) => (Err(error), cache)", "consumed == 0",
                    "part2_jpip_response_data(cache, header, body, position, messages)",
                    "Err(error) => (Err(error), data.1)", "next > usize::MAX as nat",
                    "next <= position as nat || next > input.len()",
                    "part2_jpip_response_remaining(input, data.1, parsed.1, parser_limits, next as usize, next_messages)",
                    "end > usize::MAX as nat", "end != input.len()", "crate::MalformedKind::TrailingData",
                    "(Ok((messages, Some(reason))), cache)",
                ),
                "part2_ingest_jpip_response": ("part2_jpip_response_remaining(input, cache, (None, None), cache.0, 0, 0)",),
            }.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole raw JPIP response requires complete raw/partial-commit/relative-error/count/EOR models")
            projections = source_text((ROOT / "src/jpip/cache_proof_support.rs").resolve())
            for name, required in {
                "jpip_response_summary_view": ("value.messages", "value.end_of_response_reason"),
                "jpip_response_outcome": ("Err(error) => Err(error)", "Ok(jpip_response_summary_view(value))"),
            }.items():
                actual = _coverage_spec_function_body(projections, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole raw JPIP response requires complete native summary/result projections")
        if entry["id"] == _JPIP_PLACEHOLDER_ENTRY:
            for field, required in (
                ("implementation_refs", _JPIP_PLACEHOLDER_IMPLEMENTATIONS),
                ("contract_refs", set(_JPIP_PLACEHOLDER_CONTRACTS)),
                ("spec_refs", _JPIP_PLACEHOLDER_MODELS), ("proof_refs", _JPIP_PLACEHOLDER_PROOFS),
                ("test_refs", _JPIP_PLACEHOLDER_TESTS),
            ):
                if not required.issubset({(ref["path"], ref["symbol"]) for ref in entry[field]}):
                    if field == "implementation_refs":
                        raise ValueError("placeholder representation selection linked function is not used by claimed implementation: actual caller missing")
                    raise ValueError("placeholder representation selection requires every native/model/result/caller/test bridge")
            constructor_path = (ROOT / "src/jp2/box_reader.rs").resolve()
            if not _coverage_verified_body_clause(
                source_text(constructor_path), function_header(constructor_path, "BoxType::new"),
                "BoxType::new", _JPIP_PLACEHOLDER_BODY_CLAUSE,
            ):
                raise ValueError("placeholder representation selection requires the checked byte/word constructor body clause")
            native_path = (ROOT / "src/jpip/reconstruction.rs").resolve()
            native = source_text(native_path)
            for name, required in {
                "placeholder_reconstruction": (
                    "if flags & 1 != 0", "PlaceholderSource::Original, original",
                    "else if flags & 2 != 0", "PlaceholderSource::Equivalent, header",
                    "None => Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents))",
                    "else if flags & 4 != 0", "PlaceholderSource::Codestream, original",
                    "PlaceholderSource::Empty, original",
                ),
                "DatabinCache::expand_metadata_bin": (
                    "let (source, header) = placeholder_reconstruction(",
                    "placeholder.flags", "&placeholder.original_header",
                    "match &placeholder.equivalent_header", "Some(header) => Some(header.as_slice())",
                    "match source", "PlaceholderSource::Equivalent =>", "jpip_superbox(box_type)",
                    "append_reconstructed_box(output, header, &payload)",
                ),
            }.items():
                body = _coverage_function_body(native, function_header(native_path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("placeholder representation selection requires the actual branch/header pair and caller framing")
            projections = {
                "placeholder_source_view": (
                    "match source",
                    "PlaceholderSource::Original => 0", "PlaceholderSource::Equivalent => 1",
                    "PlaceholderSource::Codestream => 2", "PlaceholderSource::Empty => 3",
                ),
                "placeholder_header_option_view": ("match header", "Some(bytes) => Some(bytes@)", "None => None"),
                "placeholder_reconstruction_outcome": (
                    "match value",
                    "Ok((source, header)) => Ok((placeholder_source_view(source), header@))",
                    "Err(error) => Err(error)",
                ),
                "placeholder_value_view": (
                    "flags: value.flags", "bin: value.bin",
                    "original_header: value.original_header@", "original_type: value.original_type",
                    "equivalent_bin: value.equivalent_bin", "match value.equivalent_header",
                    "Some(header) => Some(header@)", "None => None",
                    "equivalent_type: value.equivalent_type", "stream: value.stream",
                    "stream_count: value.stream_count",
                ),
                "placeholder_parse_outcome": (
                    "Ok(value) => Ok(placeholder_value_view(value))", "Err(error) => Err(error)",
                ),
            }
            model = source_text((ROOT / "specs/jpip_layout.rs").resolve())
            for text, functions in (
                (native, projections),
                (model, {"part2_jpip_placeholder_reconstruction": (
                    "if flags & 1 != 0", "Ok((0, original))", "else if flags & 2 != 0",
                    "Some(header) => Ok((1, header))",
                    "None => Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidBoxContents))",
                    "else if flags & 4 != 0", "Ok((2, original))", "Ok((3, original))",
                ),
                    "part2_jpip_placeholder_header": (
                        "part2_jpip_read_u32(input, position)", "if length == 1 { 16 } else { 8 }",
                        "end > usize::MAX as nat", "end > input.len()",
                        "input.subrange(position as int, end as int)", "box_type_from_word_model(",
                    ),
                    "part2_jpip_placeholder_equivalent": (
                        "flags & 6 == 0", "Ok((None, None, None, position))",
                        "part2_jpip_read_u64(input, position)", "position as nat + 8 > usize::MAX as nat",
                        "part2_jpip_placeholder_header(input, (position + 8) as usize)",
                        "Some(part2_jpip_copy_bytes(header.0))", "Some(header.1), header.2",
                    ),
                    "part2_jpip_placeholder_stream": (
                        "flags & 4 == 0", "Ok((None, 0, position))", "part2_jpip_read_u64(input, position)",
                        "flags & 8 != 0", "part2_jpip_read_u32(input, after)", "count == 0",
                        "input.len() == after as nat + 4", "Ok(_) =>", "Ok((Some(stream), 1, (after + 4) as usize))",
                    ),
                    "part2_jpip_parse_placeholder": (
                        "input.len() < 20", "part2_jpip_read_u32(input, 0)",
                        "part2_jpip_read_u32(input, 4)", "part2_jpip_read_u32(input, 8)",
                        "part2_jpip_placeholder_header(input, 12)", "flags & !0x0f != 0",
                        "flags & 8 != 0 && flags & 4 == 0",
                        "part2_jpip_placeholder_equivalent(input, flags, original.2)",
                        "part2_jpip_placeholder_stream(input, flags, equivalent.3)",
                        "stream.2 as nat != input.len()", "flags == 4 && input.len() == original.2 as nat + 24",
                        "original.2 as u64", "bin: ((high as u64) << 32) | low as u64",
                        "original_header: part2_jpip_copy_bytes(original.0)", "original_type: original.1",
                        "equivalent_bin: equivalent.0", "equivalent_header: equivalent.1",
                        "equivalent_type: equivalent.2", "stream: stream.0", "stream_count: stream.1",
                    ),
                }),
                (source_text((ROOT / "specs/jpip_transitions.rs").resolve()), {
                    "part2_jpip_read_u64": (
                        "part2_jpip_read_u32(input, position)", "position as nat + 4 > usize::MAX as nat",
                        "part2_jpip_read_u32(input, (position + 4) as usize)",
                        "Ok(low) => Ok(((high as u64) << 32) | low as u64)",
                    ),
                }),
            ):
                for name, required in functions.items():
                    body = _coverage_spec_function_body(text, name)
                    if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                        raise ValueError("placeholder representation selection requires complete raw header/error/result models")
        if entry["id"] == _JPIP_LAYOUT_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPIP_LAYOUT_CONTRACTS) - _JPIP_LAYOUT_APIS:
                raise ValueError("whole JPIP layout Results require the complete actual reconstruction consumer contract")
            for field, required in (
                ("implementation_refs", _JPIP_LAYOUT_IMPLEMENTATIONS), ("spec_refs", _JPIP_LAYOUT_MODELS),
                ("proof_refs", _JPIP_LAYOUT_PROOFS), ("test_refs", _JPIP_LAYOUT_TESTS),
            ):
                if not required.issubset({(ref["path"], ref["symbol"]) for ref in entry[field]}):
                    if field == "implementation_refs":
                        raise ValueError("whole JPIP layout Results linked function is not used by claimed implementation: actual public entrypoints missing")
                    raise ValueError("whole JPIP layout Results require every actual cache/layout/byte/error/test bridge")
            for relative, functions in (
                ("src/jpip/reconstruction.rs", {
                    "DatabinCache::reconstruct_codestream": (
                        "layout.len() < 3 || layout.len() & 1 == 0",
                        "first.class, DatabinClass::MainHeader", "first.in_class != 0",
                        "pair.checked_add(1)", "layout.get(pair)", "layout.get(data_index)",
                        "header.class, DatabinClass::TileHeader", "data.class, DatabinClass::TileData",
                        "header.codestream != first.codestream", "data.codestream != first.codestream",
                        "header.in_class != data.in_class", "pair += 2", "self.reconstruct(layout)?",
                        "!view.bytes.starts_with(&SOC) || !view.bytes.ends_with(&EOC)", "Ok(view)",
                        "part2_jpip_codestream_pairs(identifiers, 1)",
                        "part2_jpip_codestream_pairs(identifiers, pair as nat)",
                    ),
                    "DatabinCache::reconstruct_container": (
                        "layout.is_empty()", "layout[index].class, DatabinClass::Metadata",
                        "index as u64", "index += 1", "self.reconstruct(layout)",
                        "part2_jpip_metadata_layout(identifiers, 0)",
                        "part2_jpip_metadata_layout(identifiers, index as nat)",
                    ),
                }),
                ("specs/jpip_layout.rs", {
                    "part2_jpip_layout_error": ("part2_jpip_cache_error(offset, crate::MalformedKind::InvalidJpipLayout)",),
                    "part2_jpip_codestream_pairs": (
                        "position >= layout.len()", "position + 1 > usize::MAX as nat",
                        "position + 1 >= layout.len()", "header.1 != crate::jpip::DatabinClass::TileHeader",
                        "data.1 != crate::jpip::DatabinClass::TileData", "header.2 != layout[0].2",
                        "data.2 != layout[0].2", "header.3 != data.3",
                        "part2_jpip_codestream_pairs(layout, position + 2)",
                    ),
                    "part2_jpip_codestream_markers": (
                        "bytes.len() >= 2", "bytes[0] == 0xff", "bytes[1] == 0x4f",
                        "bytes[bytes.len() - 2] == 0xff", "bytes[bytes.len() - 1] == 0xd9",
                    ),
                    "part2_jpip_cache_codestream": (
                        "layout.len() < 3 || layout.len() % 2 == 0",
                        "layout[0].1 != crate::jpip::DatabinClass::MainHeader", "layout[0].3 != 0",
                        "part2_jpip_codestream_pairs(layout, 1)", "part2_jpip_cache_reconstruct(cache, layout)",
                        "part2_jpip_codestream_markers(bytes)", "crate::MalformedKind::MissingRequiredStructure",
                    ),
                    "part2_jpip_metadata_layout": (
                        "position >= layout.len()", "layout[position as int].1 != crate::jpip::DatabinClass::Metadata",
                        "part2_jpip_layout_error(position as u64)", "part2_jpip_metadata_layout(layout, position + 1)",
                    ),
                    "part2_jpip_cache_container": (
                        "layout.len() == 0", "part2_jpip_metadata_layout(layout, 0)",
                        "part2_jpip_cache_reconstruct(cache, layout)",
                    ),
                }),
            ):
                path = (ROOT / relative).resolve()
                text = source_text(path)
                for name, required in functions.items():
                    body = (_coverage_spec_function_body(text, name) if relative.startswith("specs/")
                            else _coverage_function_body(text, function_header(path, name)))
                    if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                        raise ValueError("whole JPIP layout Results require original ordered admission/cache/marker handoffs")
        if entry["id"] == _JPIP_CACHE_INSERT_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPIP_CACHE_INSERT_CONTRACTS):
                raise ValueError("whole JPIP cache insertion requires the complete actual Result/cache-state contract")
            if not _JPIP_CACHE_INSERT_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _JPIP_CACHE_INSERT_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}) \
                    or not _JPIP_CACHE_INSERT_TESTS.issubset({(ref["path"], ref["symbol"]) for ref in entry["test_refs"]}):
                raise ValueError("whole JPIP cache insertion requires every actual clone/traversal/copy/commit/caller/test bridge")
            if not _JPIP_CACHE_INSERT_IMPLEMENTATIONS.issubset(
                    {(ref["path"], ref["symbol"]) for ref in entry["implementation_refs"]}):
                raise ValueError("whole JPIP cache insertion linked function is not used by claimed implementation: actual callers missing")
            path = (ROOT / "src/jpip/cache.rs").resolve()
            text = source_text(path)
            for name, required in {
                "DatabinCache::insert": (
                    "!crate::refinement::jpip_standard_class_assigned(fragment.databin.class_identifier())",
                    "let ghost original_cache = jpip_cache_view(self)", "let ghost original_owner = *self",
                    "let ghost incoming = jpip_fragment_view(&fragment)", "part2_jpip_insert_result(original_cache, incoming)",
                    "self.accepted_fragments.checked_add(1)", "next_count > self.limits.maximum_jpip_fragments()",
                    "self.find_databin_index(fragment.databin)", ".clone()", "databin.validate_final_length(&fragment, incoming_end)?",
                    "databin.fragments[first].end() < fragment.offset", "databin.fragments[last].offset <= merged_end",
                    "stored.bytes.get(stored_start..stored_end)", "stored_overlap == incoming_overlap",
                    "jpip_merge_start(merged_start, stored.offset)", "jpip_merge_end(merged_end, stored.end())",
                    "merged_end.checked_sub(merged_start)", "checked_sub(replaced_bytes)",
                    "self.stored_bytes.checked_add(added_bytes)", "new_stored_bytes > self.limits.maximum_input_bytes()",
                    "vec![0_u8; merged_length]", "copy_into(&mut merged, start, &stored.bytes, stored.offset)?",
                    "copy_into(&mut merged, incoming_start, &fragment.bytes, fragment.offset",
                    "databin.normalize_fragments(first, last, merged_start, merged)?",
                    "jpip_transaction_commit(true)", "self.databins[index] = databin", "self.databins.push(databin)",
                    "self.stored_bytes = new_stored_bytes", "self.accepted_fragments = next_count",
                    "expected == part2_jpip_insert_result(original_cache, incoming)",
                ),
                "Databin::validate_final_length": (
                    "incoming_end > final_length", "jpip_final_length_consistent(final_length, new_final)",
                    "self.fragments[stored_index].end() > new_final", "self.final_length = Some(new_final)",
                ),
                "Databin::normalize_fragments": (
                    "self.fragments.len().checked_add(1)", ".get(prefix_index)", ".get(suffix_index)",
                    ".clone()", "normalized.push(StoredFragment", "bytes: merged", "self.fragments = normalized",
                ),
            }.items():
                body = _coverage_function_body(text, function_header(path, name))
                missing = list(required) if body is None else [
                    item for item in required if "".join(item.split()) not in "".join(body.split())
                ]
                if missing:
                    raise ValueError(
                        f"whole JPIP cache insertion requires original actual admission/overlap/copy/normalization/commit handoffs: {name}: {missing}"
                    )
            header = function_header(path, "DatabinCache::insert")
            start = text.rfind("#[cfg_attr(verus_keep_ghost, verus_spec(", 0, header.start())
            if "*final(self)==*old(self)" not in "".join(text[start:header.start()].split()):
                raise ValueError("whole JPIP cache insertion requires the native-owner error frame")
            model_path = (ROOT / "specs/jpip_cache_insert.rs").resolve()
            model = source_text(model_path)
            for name, required in {
                "part2_jpip_insert_result": ("!part9_standard_class_assigned(incoming.0.0 as nat)",
                    "part2_jpip_error(0, crate::MalformedKind::InvalidJpipHeader)",
                    "cache.3 as nat + 1", "resource_jpip_fragment_limit(&cache.0)",
                    "part2_jpip_find_databin(cache.1, incoming.0, 0)", "cache.1[index as int]", "(incoming.0, Seq::empty(), None)"),
                "part2_jpip_cache_insert": ("part2_jpip_insert_result(cache, incoming)", "Err(error) => (Err(error), cache)", "Ok(updated) => (Ok(()), updated)"),
                "part2_jpip_insert_overlap": ("stored.1.subrange", "incoming.2.subrange", "usize::MAX", "part2_jpip_insert_conflict(start)"),
                "part2_jpip_insert_merge": ("stored[position as int].0 > end", "part2_jpip_insert_overlap(fragment, incoming, incoming_end)",
                    "position + 1", "part2_jpip_stored_end(fragment)"),
                "part2_jpip_insert_final_state": ("end > length", "old_length != length", "part2_jpip_insert_final_scan(bin.1, length, position)"),
                "part2_jpip_insert_final_scan": ("position >= stored.len()", "part2_jpip_stored_end(stored[position as int]) > length", "position + 1"),
                "part2_jpip_insert_account": ("(length as u64) < replaced", "cache.2 as nat", "u64::MAX",
                    "total > crate::limits::resource_input_byte_limit(&cache.0)", "Seq::new(length as nat, |_: int| 0u8)"),
                "part2_jpip_insert_copy": ("stored.0 < start", "usize::MAX", "part2_jpip_copy_into(output"),
                "part2_jpip_insert_normalize": ("stored.subrange(0, first as int)", "seq![(start, bytes)]",
                    "stored.subrange(last as int, stored.len() as int)"),
                "part2_jpip_insert_commit": ("bin.1.len() + 1 > usize::MAX", "cache.1.push(updated)", "cache.1.update(index as int, updated)", "total, count"),
            }.items():
                body = _coverage_spec_function_body(model, name)
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole JPIP cache insertion requires complete original-state/input-derived error and normalized-byte models")
            clone_path = (ROOT / "src/jpip.rs").resolve()
            clones = source_text(clone_path)
            for name, required in {
                "StoredFragment::clone": ("offset: self.offset", "bytes: self.bytes.clone()"),
                "Databin::clone": ("id: self.id.clone()", "fragments: self.fragments.clone()", "final_length: self.final_length.clone()"),
            }.items():
                body = _coverage_function_body(clones, function_header(clone_path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole JPIP cache insertion requires the original checked field-clone operations")
        if entry["id"] == _JPIP_CACHE_VIEW_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPIP_CACHE_VIEW_CONTRACTS):
                raise ValueError("whole JPIP cache view Results require all five actual status/view/prefix/reconstruction contracts")
            if not _JPIP_CACHE_VIEW_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _JPIP_CACHE_VIEW_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}) \
                    or not _JPIP_CACHE_VIEW_TESTS.issubset({(ref["path"], ref["symbol"]) for ref in entry["test_refs"]}):
                raise ValueError("whole JPIP cache view Results require every physical/lookup/status/layout/owned/error/test bridge")
            if not (set(_JPIP_CACHE_VIEW_CONTRACTS) | _JPIP_CACHE_VIEW_CALLERS).issubset(
                    {(ref["path"], ref["symbol"]) for ref in entry["implementation_refs"]}):
                raise ValueError("whole JPIP cache view Results linked function is not used by claimed implementation: actual callers missing")
            path = (ROOT / "src/jpip/cache.rs").resolve()
            text = source_text(path)
            for name, required in {
                "DatabinCache::status": ("self.find_databin_index(id)?", "self.databins.get(index)?",
                    "jpip_databin_fields(databin)", "bytes.saturating_add(fragment.bytes.len() as u64)",
                    "fragment.offset == prefix", "prefix = fragment.end()", "final_length: databin.final_length",
                    "contiguous_prefix: prefix", "stored_bytes: bytes", "intervals: databin.fragments.len() as u64",
                    "index += 1; } #[cfg(verus_keep_ghost)] proof! { reveal(crate::specs::part2_jpip_status_scan)"),
                "DatabinCache::is_complete": ("self.status(id)", "Some(status) => status.is_complete()", "None => false"),
                "DatabinCache::databin_view": ("self.find_databin_index(id)", "self.databins.get(index)", "self.status(id)",
                    "status.is_complete()", "status.contiguous_prefix", "databin.fragments.is_empty()",
                    "databin.fragments[0].bytes.clone()", "Ok(JpipByteView { bytes })"),
                "DatabinCache::databin_prefix": ("self.find_databin_index(id)", "self.databins.get(index)",
                    "databin.fragments.first()", "first.offset != 0", "first.bytes.clone()"),
                "DatabinCache::reconstruct": ("let ghost cache = jpip_cache_view(self)", "let ghost identifiers = jpip_layout_view(layout)",
                    "self.databin_view(layout[index])?", "total.checked_add(view.bytes.len() as u64)",
                    "total > self.limits.maximum_input_bytes()", "parts.push(view)",
                    "jpip_reconstruction_length(total, 0, 0, 0)", "usize::try_from(contracted_total)",
                    "part2_jpip_reconstruct_error_persists", "bytes.extend_from_slice(&parts[part_index].bytes)",
                    "part2_jpip_reconstruct_prefix(cache, identifiers, index as nat)", "jpip_view_parts(&parts)",
                    "part2_jpip_flatten_prefix(jpip_view_parts(&parts), part_index as nat)"),
            }.items():
                body = _coverage_function_body(text, function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole JPIP cache view Results require actual first-match/ordered-scan/clone/layout/error handoffs")
            model = source_text((ROOT / "specs/jpip_cache_views.rs").resolve())
            for name, required in {
                "part2_jpip_cache_error": ("part2_jpip_fragment_error(offset, kind)",),
                "part2_jpip_status_scan": ("position >= fragments.len()", "bytes as nat + (fragment.1.len() as u64) as nat",
                    "total > u64::MAX as nat", "fragment.0 == prefix", "part2_jpip_stored_end(fragment)",
                    "part2_jpip_status_scan(fragments, position + 1, next_prefix, next_bytes)"),
                "part2_jpip_databin_status": ("part2_jpip_status_scan(databin.1, 0, 0, 0)", "(databin.2, scan.0, scan.1, databin.1.len() as u64)"),
                "part2_jpip_cache_status": ("part2_jpip_find_databin(cache.1, id, 0)", "index as nat >= cache.1.len()", "part2_jpip_databin_status(cache.1[index as int])"),
                "part2_jpip_cache_complete": ("part2_jpip_cache_status(cache, id)", "None => false", "part2_jpip_status_complete(status)"),
                "part2_jpip_cache_view": ("part2_jpip_find_databin(cache.1, id, 0)", "part2_jpip_cache_status(cache, id)",
                    "part2_jpip_cache_error(status.1", "ArithmeticOverflow", "fragments[0].1"),
                "part2_jpip_cache_prefix": ("part2_jpip_find_databin(cache.1, id, 0)", "index as nat >= cache.1.len()",
                    "fragments.len() == 0 || fragments[0].0 != 0", "fragments[0].1"),
                "part2_jpip_reconstruct_prefix": ("position == 0", "part2_jpip_reconstruct_prefix(cache, layout, (position - 1) as nat)",
                    "part2_jpip_cache_view(cache, layout[position as int - 1])", "total > u64::MAX as nat",
                    "resource_input_byte_limit(&cache.0)", "actual: total as u64", "previous.0.push(bytes)"),
                "part2_jpip_flatten_prefix": ("position == 0", "part2_jpip_flatten_prefix(parts, (position - 1) as nat) + parts[position as int - 1]"),
                "part2_jpip_cache_reconstruct": ("part2_jpip_reconstruct_prefix(cache, layout, layout.len())",
                    "part9_reconstruction_length(parts.1 as nat, 0, 0, 0)", "length > usize::MAX as nat",
                    "part2_jpip_flatten_prefix(parts.0, parts.0.len())"),
            }.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole JPIP cache view Results require complete ordered-status/first-bytes/layout/error models")
            projections = source_text((ROOT / "src/jpip/cache_proof_support.rs").resolve())
            for name, required in {
                "jpip_cache_view": ("value.limits", "value.databins@", "jpip_databin_view(&databin)", "value.stored_bytes", "value.accepted_fragments"),
                "jpip_databin_view": ("value.fragments@", "jpip_stored_fragment_view(&fragment)", "value.final_length"),
                "jpip_status_view": ("value.final_length", "value.contiguous_prefix", "value.stored_bytes", "value.intervals"),
                "jpip_byte_view": ("value.bytes@",),
                "jpip_byte_outcome": ("Err(error) => Err(error)", "Ok(jpip_byte_view(&value))"),
                "jpip_status_outcome": ("None => None", "Some(jpip_status_view(&value))"),
                "jpip_layout_view": ("value@.map_values", "databin_id_view(id)"),
                "jpip_view_parts": ("value@.map_values", "jpip_byte_view(&part)"),
            }.items():
                actual = _coverage_spec_function_body(projections, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole JPIP cache view Results require physical cache/layout/owned byte and status projections")
        if entry["id"] == _JPIP_FRAGMENT_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPIP_FRAGMENT_CONTRACTS):
                raise ValueError("whole JPIP entry foundations require actual byte-copy/point-copy/normalized-lookup contracts")
            if not _JPIP_FRAGMENT_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _JPIP_FRAGMENT_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}) \
                    or not _JPIP_FRAGMENT_TESTS.issubset({(ref["path"], ref["symbol"]) for ref in entry["test_refs"]}):
                raise ValueError("whole JPIP entry foundations require every owned/raw/header/cache/status/byte/move/test bridge")
            path = (ROOT / "src/jpip/cache.rs").resolve()
            text = source_text(path)
            for name, clause in _JPIP_FRAGMENT_BODY_CLAUSES.items():
                if not _coverage_verified_body_clause(text, function_header(path, name), name, clause):
                    raise ValueError("whole JPIP entry foundations require exact checked constructor body clauses: " + name)
            for name, clause in _JPIP_FRAGMENT_GETTERS.items():
                header = function_header(path, name)
                if header is None:
                    raise ValueError("whole JPIP entry foundations require exact native getter declarations")
                signature = text.find("fn", header.start(), header.end())
                attrs = text[text.rfind("#[cfg_attr", 0, signature):signature]
                if "ensures" + "".join(clause.split()) + "," not in "".join(attrs.split()) or re.search(r"\brequires\b", attrs):
                    raise ValueError("whole JPIP entry foundations require complete stored getter/value/move frames")
            for name, required in {
                "JpipFragment::new": ("bytes.is_empty() && !is_final", "let length = bytes.len() as u64",
                    "offset.checked_add(length)", "jpip_fragment_valid(offset, length, limits.maximum_input_bytes())",
                    "bytes,", "final_length: if is_final { Some(end) } else { None }", "auxiliary,"),
                "JpipFragment::from_message": ("body.len() as u64 != header.length", "header.offset",
                    "Self::new(header.databin, header.offset, copy_bytes(body), header.last_byte, header.auxiliary, limits,)"),
                "DatabinCache::new": ("limits,", "databins: Vec::new()", "stored_bytes: 0", "accepted_fragments: 0"),
                "DatabinCache::find_databin_index": ("jpip_cache_fields(self)", "self.databins[index].id.same_as(id)",
                    "return Some(index)", "index += 1", "part2_jpip_find_databin(jpip_cache_view(self).1, databin_id_view(id), index as nat)"),
                "copy_bytes": ("Vec::with_capacity(input.len())", "output@ == input@.subrange(0, index as int)", "output.push(input[index])"),
                "copy_into": ("output_start.checked_add(input.len())", "get_mut(output_start..output_end)", "target.copy_from_slice(input)"),
            }.items():
                body = _coverage_function_body(text, function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole JPIP entry foundations require actual raw/owned/header/lookup/copy handoffs")
            model = source_text((ROOT / "specs/jpip_fragment.rs").resolve())
            for name, required in {
                "part2_jpip_fragment_new": ("bytes.len() == 0 && !last", "offset as nat + length as nat",
                    "end > u64::MAX as nat", "valid_jpip_fragment", "actual: end as u64",
                    "Ok((databin, offset, bytes, if last { Some(end as u64) } else { None }, auxiliary))"),
                "part2_jpip_fragment_from_message": ("body.len() as u64 != header.2", "header.1",
                    "part2_jpip_fragment_new(header.0, header.1, body, header.3, header.4, limits)"),
                "part2_jpip_stored_end": ("fragment.0 as nat + (fragment.1.len() as u64) as nat", "end > u64::MAX as nat"),
                "part2_jpip_copy_into": ("start as nat + input.len()", "end > usize::MAX as nat || end > output.len()",
                    "ArithmeticOverflow)), output", "Seq::new(output.len()", "input[index - start as int]", "output[index]"),
                "part2_jpip_empty_cache": ("(limits, Seq::empty(), 0, 0)",),
                "part2_jpip_find_databin": ("position >= databins.len()", "part2_jpip_identity(databins[position as int].0, id)",
                    "Some(position as usize)", "part2_jpip_find_databin(databins, id, position + 1)"),
                "part2_jpip_status_complete": ("None => false", "complete_jpip_databin(status.1 as nat, length as nat)"),
            }.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole JPIP entry foundations require complete raw/owned/header/cache/copy/status models")
            projections = source_text((ROOT / "src/jpip/cache_proof_support.rs").resolve())
            for name, required in {
                "jpip_fragment_view": ("databin_id_view(value.databin)", "value.offset", "value.bytes@", "value.final_length", "value.auxiliary"),
                "jpip_fragment_new_input": ("part2_jpip_fragment_new(databin_id_view(databin), offset, bytes@, last, auxiliary, limits)",),
                "jpip_fragment_message_input": ("part2_jpip_fragment_from_message(jpip_header_view(header), body@, limits)",),
                "jpip_cache_view": ("value.limits", "value.databins@", "jpip_databin_view(&databin)", "value.stored_bytes", "value.accepted_fragments"),
                "jpip_databin_view": ("databin_id_view(value.id)", "value.fragments@", "jpip_stored_fragment_view(&fragment)", "value.final_length"),
                "jpip_stored_fragment_view": ("(value.offset, value.bytes@)",),
                "jpip_status_view": ("(value.final_length, value.contiguous_prefix, value.stored_bytes, value.intervals)",),
                "jpip_byte_view": ("value.bytes@",),
                "jpip_byte_storage": ("&value.bytes",),
            }.items():
                actual = _coverage_spec_function_body(projections, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole JPIP entry foundations require complete physical entry/owned-storage/cache projections")
        if entry["id"] == _JPIP_MESSAGE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPIP_MESSAGE_CONTRACTS) - _JPIP_MESSAGE_BOUNDARIES:
                raise ValueError("whole raw JPIP message Results require actual message/parser/EOR/VBAS contracts")
            if not _JPIP_MESSAGE_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _JPIP_MESSAGE_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}) \
                    or not _JPIP_MESSAGE_TESTS.issubset({(ref["path"], ref["symbol"]) for ref in entry["test_refs"]}):
                raise ValueError("whole raw JPIP message Results require every raw/context/cursor/header/body/static/getter/test bridge")
            path = (ROOT / "src/jpip/message.rs").resolve()
            text = source_text(path)
            for name, clause in _JPIP_MESSAGE_BODY_CLAUSES.items():
                header = function_header(path, name)
                if not _coverage_verified_body_clause(text, header, name, clause):
                    raise ValueError("whole raw JPIP message Results require exact checked impl body clauses without trust or premises: " + name)
            for name, clause in _JPIP_MESSAGE_GETTERS.items():
                header = function_header(path, name)
                if header is None:
                    raise ValueError("whole raw JPIP message Results require actual getter declaration")
                signature = text.find("fn", header.start(), header.end())
                attrs = text[text.rfind("#[cfg_attr", 0, signature):signature]
                if "ensures" + "".join(clause.split()) + "," not in "".join(attrs.split()) or re.search(r"\brequires\b", attrs):
                    raise ValueError("whole raw JPIP message Results require complete stored getter value/reference frames")
            for name, required in {
                "DatabinClass::from_identifier": ("jpip_standard_class_assigned(identifier)",
                    "2 => Some(Self::TileHeader)", "6 => Some(Self::MainHeader)"),
                "DatabinId::from_wire": ("matches!(class_identifier, 3 | 7)", "class: DatabinClass::Unassigned",
                    "Self::new(class_identifier, codestream, in_class)"),
                "parse_jpip_message": ("input.is_empty()", "input.len() as u64 > limits.maximum_input_bytes()",
                    "input[0] == 0", "parse_end_of_response(input)", "read_vbas(input, &mut position, Some(0x0f))",
                    "context.previous_class", "context.previous_codestream", "DatabinId::from_wire(class_identifier, codestream, in_class)",
                    "context.previous_class.unwrap_or(0)", "context.previous_codestream.unwrap_or(0)",
                    "context.previous_class = Some(class_identifier)", "context.previous_codestream = Some(codestream)",
                    "parse_data_after_identity(input, position, databin, last_byte, limits)?", "Ok(parsed)"),
                "parse_data_after_identity": ("read_vbas(input, &mut position, None)",
                    "DatabinClass::has_auxiliary(databin.class_identifier)", "offset.checked_add(length)",
                    "end > limits.maximum_input_bytes()", "usize::try_from(length)",
                    "position.checked_add(body_length)", "body_end > input.len()",
                    "databin,", "offset,", "length,", "last_byte,", "auxiliary,", "header_length: position",
                    "body: &input[position..body_end]", "body_end"),
                "read_vbas": ("let start = *position", "first_mask.unwrap_or(0x7f)",
                    "let mut value = u64::from(first & mask)", "count >= MAX_VBAS_BYTES", "checked_mul(128)", "shifted.checked_add(u64::from(group))",
                    "jpip_vbas_step(value, group)", "*position = position.checked_add(1)", "Ok(value)",
                    "start == *old(position)", "part2_jpip_vbas_tail(input@, start, *position, value, byte, count)"),
                "parse_end_of_response": ("input.len() < 2", "let reason_code = input[1]", "let mut position = 2_usize",
                    "read_vbas(input, &mut position, None)", "jpip_eor_extent(position, body_length)",
                    "body: &input[position..body_end]", "header_length: position"),
                "JpipMessageParser::parse": ("parse_jpip_message(input, &mut self.context, &self.limits)",),
            }.items():
                body = _coverage_function_body(text, function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw JPIP message Results require actual raw/inherited/context/cursor/body/parser handoffs")
            model = source_text((ROOT / "specs/jpip_message.rs").resolve())
            for name, required in {
                "part2_jpip_class": ("2 => Some(crate::jpip::DatabinClass::TileHeader)",
                    "6 => Some(crate::jpip::DatabinClass::MainHeader)", "_ => None"),
                "part2_jpip_wire_databin": ("identifier == 3 || identifier == 7",
                    "crate::jpip::DatabinClass::Unassigned", "part2_jpip_databin(identifier, codestream, bin)"),
                "part2_jpip_vbas_tail": ("byte & 0x80 == 0", "count >= 10", "position as nat >= input.len()",
                    "input[position as int]", "value as nat * 128 + group as nat", "stepped > u64::MAX as nat",
                    "part2_jpip_vbas_tail(input, start,", "InvalidJpipVbas"),
                "part2_jpip_read_vbas": ("start as nat >= input.len()", "input[start as int]", "let value = first & match mask",
                    "None => 0x7f", "Some(mask) => mask", "part2_jpip_vbas_tail(input, start,"),
                "part2_jpip_body": ("length as nat > usize::MAX as nat", "position as nat + length as nat > usize::MAX as nat",
                    "end as nat > input.len()", "input.subrange(position as int, end as int)"),
                "part2_jpip_eor": ("input.len() < 2", "part2_jpip_read_vbas(input, 2, None)",
                    "part2_jpip_body(input, length.1, value)", "reason: input[1]", "header_length: length.1"),
                "part2_jpip_data": ("part9_header_form_valid", "part2_jpip_read_vbas(input, 0, Some(0x0f))",
                    "part9_header_has_explicit_class", "part9_header_has_explicit_codestream", "context.0", "context.1",
                    "match context.0 { None => Ok(0), Some(value) => Ok(value) }",
                    "match context.1 { Some(value) => Ok(value), None => Ok(0) }",
                    "part2_jpip_wire_databin(class_value, stream_value, bin_value)",
                    "part2_jpip_data_after_identity"),
                "part2_jpip_data_after_identity": ("part2_jpip_read_vbas(input, position, None)",
                    "part2_jpip_read_vbas(input, offset.1, None)", "part9_auxiliary_present", "offset_value as nat + length_value as nat",
                    "end > u64::MAX as nat", "end > crate::limits::resource_input_byte_limit(limits)",
                    "part2_jpip_body(input, auxiliary.1, length_value)", "header: (databin, offset_value, length_value, last, auxiliary_value, auxiliary.1)"),
                "part2_parse_jpip_message": ("input.len() == 0", "input.len() as u64 > crate::limits::resource_input_byte_limit(limits)",
                    "input[0] == 0", "part2_jpip_eor(input)", "part2_jpip_data(input, context, limits)",
                    "(Some(header.0.0), Some(header.0.2))", "_ => context", "(parsed, next)"),
                "part2_jpip_parser_parse": ("part2_parse_jpip_message(input, parser.0, &parser.1)", "(parsed.0, (parsed.1, parser.1))"),
            }.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole raw JPIP message Results require complete raw/partial-cursor/context/header/body/parser models")
            projections = source_text((ROOT / "src/jpip/proof_support.rs").resolve())
            for name, expected in {
                "databin_id_view": "(value.class_identifier, value.class, value.codestream, value.in_class)",
                "databin_id_outcome": "match value { Err(error) => Err(error), Ok(value) => Ok(databin_id_view(value)) }",
                "jpip_context_view": "(value.previous_class, value.previous_codestream)",
                "jpip_parser_context": "jpip_context_view(value.context)",
                "jpip_parser_limits": "&value.limits",
                "jpip_parser_view": "(jpip_parser_context(value), *jpip_parser_limits(value))",
                "jpip_header_view": "(databin_id_view(value.databin), value.offset, value.length, value.last_byte, value.auxiliary, value.header_length)",
                "jpip_eor_view": "(value.reason_code, value.body@, value.header_length)",
                "jpip_eor_body_reference": "value.body",
                "jpip_message_view": """match value {
                    JpipMessage::Data { header, body } => crate::specs::Part2JpipMessage::Data { header: jpip_header_view(header), body: body@ },
                    JpipMessage::EndOfResponse(value) => crate::specs::Part2JpipMessage::EndOfResponse {
                        reason: value.reason_code, body: value.body@, header_length: value.header_length,
                    },
                }""",
                "jpip_message_outcome": "match value { Err(error) => Err(error), Ok(value) => Ok((jpip_message_view(value.0), value.1)) }",
                "jpip_message_body_reference": "match value { JpipMessage::Data { body, .. } => *body, JpipMessage::EndOfResponse(end) => end.body }",
            }.items():
                actual = _coverage_spec_function_body(projections, name)
                if actual is None or "".join(actual.split()) != "".join(expected.split()):
                    raise ValueError("whole raw JPIP message Results require complete native field/stored-reference projections")
        if entry["id"] == _RAW_JPX_PUBLIC_IMAGE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_RAW_JPX_PUBLIC_IMAGE_CONTRACTS) - _RAW_JPX_PUBLIC_IMAGE_APIS:
                raise ValueError("whole raw JPX image Results require actual raw/selected-file/layout/header/typed/color producer contracts")
            if not _RAW_JPX_PUBLIC_IMAGE_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _RAW_JPX_PUBLIC_IMAGE_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}) \
                    or not _RAW_JPX_PUBLIC_IMAGE_TESTS.issubset({(ref["path"], ref["symbol"]) for ref in entry["test_refs"]}):
                raise ValueError("whole raw JPX image Results require all public/selected/actual-header/layout-info/value/color/test bridges")
            path = (ROOT / "src/decode/api.rs").resolve()
            for name, selected, color in (
                ("decode_jpx_codestream", False, False), ("decode_jpx_codestream_selected", True, False),
                ("decode_jpx_codestream_color", False, True), ("decode_jpx_codestream_color_selected", True, True),
            ):
                body = _coverage_function_body(source_text(path), function_header(path, name))
                required = ["jp2::parse(input, options.limits())?", "jp2::raw_render_file_known(&file)"]
                required.append(("decode_jpx_file_selected" if selected else "decode_jpx_file")
                    + "(&file, codestream_index, options" + (", &expanded" if color and selected else ", selection" if selected else "") + ")?")
                if color and selected:
                    required.extend(("!file.file_type().is_jpx_compatible()",
                        "color_selection(file.codestream(codestream_index)?.data(), selection, options.limits(),)?",
                        "convert_associated_selected_color(&decoded, header, target, options.limits())"))
                elif color:
                    required.append("convert_associated_color(&decoded, header, options.limits())")
                else:
                    required.append("Ok(decoded)")
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw JPX image Results require actual raw/index/selection/header/color/target handoffs")
            path = (ROOT / "src/decode/output.rs").resolve()
            text = source_text(path)
            header = function_header(path, "decode_jpx_file_selected")
            body = _coverage_function_body(text, header)
            if header is None or header[1] or body is None or any("".join(item.split()) not in "".join(body.split()) for item in (
                "!file.file_type().is_jpx_compatible()", "file.codestream(codestream_index)?",
                "match selected.codestream_header()", "association.parsed_header()", "None => Some(file.header())",
                "association.box_header().offset()", "codestream::parse_layout(selected.data(), options.limits())?",
                "jp2::validate_selected_header(header, &layout.info, selected.box_header().offset())?",
                "typed_layout(&layout, decode_layout_selected(&layout, selection, options.limits())?, selection.discard_levels(), options.limits(),)?",
                "apply_jp2_output(decoded, header, options.limits())?", "Ok((image, associated_header))",
                "codestream::decoder_layout_main_info_matches_raw(&layout)",
                "jp2::associated_header_reference_selectors(selected, jp2::jpx_file_header_reference(file))",
            )) or any(name + "(" in "".join(body.split()) for name in ("decode_typed_layout", "decode_codestream_selected", "validate_part1_output_shape")):
                raise ValueError("whole raw JPX image Results require actual module-level selected producer and its retained layout/typed/error path")
            signature = text.find("fn", header.start(), header.end())
            attrs = text[text.rfind("#[cfg_attr", 0, signature):signature]
            stored = "Ok(output) => output.1 == jp2::jpx_file_associated_header_reference(file, codestream_index)"
            if "".join(stored.split()) not in "".join(attrs.split()) or re.search(r"\brequires\b", attrs):
                raise ValueError("whole raw JPX image Results lacks executable Verus contract: complete actual selected returned-header reference frame")
            for name, symbol, required in (
                ("specs/jpx_public_images.rs", "part2_decode_raw_jpx_typed",
                 ("part2_parse_container(input, *limits)", "part2_raw_jpx_decode_input(file)", "part2_decode_jpx_file_request(", "Ok(decoded.0)")),
                ("specs/jpx_public_images.rs", "part2_decode_raw_jpx_color",
                 ("part2_parse_container(input, *limits)", "part2_raw_jpx_decode_input(raw)", "part2_decode_jpx_selected_color(file, index, limits, requested)",
                  "part2_decode_jpx_codestream(file, index, limits)", "part2_convert_associated(decoded.0, decoded.1,")),
                ("specs/jpx_public_images.rs", "part2_decode_jpx_selected_file",
                 ("!part2_file_type_jpx(input.0)", "part2_jpx_codestream_lookup(input.1, index)", "part2_decode_jpx_selected_source(source, input.2, limits, requested)")),
                ("specs/jpx_public_images.rs", "part2_decode_jpx_selected_source",
                 ("part2_associated_codestream_header(source.2, fallback)", "part1_parse_layout(source.0, limits)",
                  "part2_decode_jpx_selected_layout(source, header, layout, limits, requested)")),
                ("specs/jpx_public_images.rs", "part2_decode_jpx_selected_layout",
                 ("layout.0.image_size", "part2_validate_selected_header(header.1, size.geometry.0, size.geometry.1, size.components,",
                  "size.uniform_bit_depth, size.uniform_signed, source.1", "part2_decoder_input_from_raw(layout)",
                  "part2_decode_layout_selected_value_input(input, requested, limits)", "part2_typed_layout_input(input, decoded, requested.2, limits)",
                  "part2_apply_output_header(image, header.0,", "Ok((mapped, Some(header)))")),
                ("specs/jpx_public_images.rs", "part2_decode_jpx_selected_color",
                 ("!part2_file_type_jpx(file.0)", "part2_jpx_codestream_lookup(file.1, index)",
                  "part2_color_selection_raw(source.0, limits, requested)", "part2_decode_jpx_selected_file(file, index, limits, expanded.0)",
                  "part2_convert_associated_selected(decoded.0, decoded.1,", "[expanded.1[0], expanded.1[1], expanded.1[2], expanded.1[3]]")),
            ):
                actual = _coverage_spec_function_body(source_text((ROOT / name).resolve()), symbol)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required) \
                        or (symbol == "part2_decode_jpx_selected_layout" and "part1_validate_typed_output_shape" in actual):
                    raise ValueError("whole raw JPX image Results require complete raw/selected-layout/header/reference/color-target models")
        if entry["id"] == _RAW_CONTAINER_COLOR_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_RAW_CONTAINER_COLOR_CONTRACTS) - _RAW_CONTAINER_COLOR_APIS:
                raise ValueError("whole raw container color Results require actual inspection/core/header/color/selection/crop producer contracts")
            if not _RAW_CONTAINER_COLOR_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _RAW_CONTAINER_COLOR_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}) \
                    or not _RAW_CONTAINER_COLOR_TESTS.issubset({(ref["path"], ref["symbol"]) for ref in entry["test_refs"]}):
                raise ValueError("whole raw container color Results require all public/raw/expanded-selection/value/header/color/test bridges")
            path = (ROOT / "src/decode/api.rs").resolve()
            for name, selected, jph in (
                ("decode_jp2_color", False, False), ("decode_jp2_color_selected", True, False),
                ("decode_jph_color", False, True), ("decode_jph_color_selected", True, True),
            ):
                body = _coverage_function_body(source_text(path), function_header(path, name))
                required = [
                    ("jp2::inspect_jph" if jph else "jp2::parse_and_inspect_for_display") + "(input, options.limits())?",
                    "inspected.file().codestream_count() != 1" if jph else "validate_jp2_display_profile(inspected.file())?",
                    "jp2::raw_render_file_known(jp2::raw_inspected_file_reference(&inspected))",
                ]
                required.extend((
                    "let codestream = inspected.file().codestream(0)?.data()",
                    "color_selection(codestream, selection, options.limits())?",
                    "decode_codestream_selected(codestream, options, &expanded)?",
                    "finish_associated_selected_output(decoded, Some(inspected.file().header()), target, options.limits(),)",
                    "part2_decode_raw_codestream_selection_value(codestream@, crate::options::decode_options_limits(options), &expanded)",
                ) if selected else (
                    "decode_codestream(inspected.file().codestream(0)?.data(), options)?",
                    "apply_jp2_output(decoded, inspected.file().header(), options.limits())?",
                    "crate::color::convert_jp2_color(&mapped, &inspected.file().header().color, options.limits())",
                ))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw container color Results require actual raw/selection/expanded/core/header/color/target handoffs")
            path = (ROOT / "src/decode/output.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "color_selection"))
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in (
                "codestream::parse_layout(input, limits)?", "let size = &layout.info.image_size",
                "color_selection_for_size(size, requested)", "codestream::decoder_layout_input_matches_raw(&layout)",
                "codestream::decoder_layout_input_fields(&layout)",
            )):
                raise ValueError("whole raw container color Results require actual raw layout expansion producer")
            for path, name, required in (
                ("specs/container_colors.rs", "part2_decode_raw_color_container",
                 ("if jph { part2_inspect_jph_container(input, limits) }", "else { part2_parse_and_inspect_container_mode(input, limits, true) }",
                  "part2_decode_file_color(inspected.0, limits, requested, jph)")),
                ("specs/container_colors.rs", "part2_decode_file_color",
                 ("jph && file.streams.len() != 1", "!jph && part2_validate_jp2_display_profile(file).is_err()",
                  "part2_raw_associated_header(file.header)",
                  "part2_decode_raw_codestream(file.streams[0].1, limits, None)",
                  "part2_apply_output_header(decoded, header.0,", "color_convert_jp2(mapped.1, mapped.2, mapped.0, header.2,",
                  "part2_color_selection_raw(file.streams[0].1, limits, requested)",
                  "part2_decode_raw_codestream_value(file.streams[0].1, limits, Some(expanded.0))",
                  "[expanded.1[0], expanded.1[1], expanded.1[2], expanded.1[3]]",
                  "part2_finish_associated_selected_output(decoded, Some(header),",
                  "crate::limits::resource_component_limit(limits)", "crate::limits::resource_decoded_bytes_limit(limits)",
                  "crate::limits::resource_work_limit(limits)")),
                ("specs/container_colors.rs", "part2_color_selection_raw",
                 ("part1_parse_layout(input, limits)", "part2_color_selection_layout(layout, requested)")),
                ("specs/container_colors.rs", "part2_color_selection_layout",
                 ("part2_decoder_input_from_raw(layout).size", "part2_color_selection_requested(",
                  "crate::codestream::selection_geometry_view(&size)", "crate::codestream::image_size_component_infos(&size)",
                  "crate::codestream::image_size_component_count(&size), requested")),
                ("specs/raw_decode.rs", "part2_decode_raw_codestream_value",
                 ("part1_parse_layout(input, limits)", "part2_decode_typed_layout_value_input(",
                  "input.len() as usize, part2_decoder_input_from_raw(layout), limits, requested")),
                ("specs/decoder_input.rs", "part2_decode_layout_selected_input",
                 ("part2_decode_layout_selected_value_input(input, crate::options::decode_selection_view(requested), limits)",)),
                ("specs/decoder_input.rs", "part2_decode_typed_layout_input",
                 ("part2_decode_typed_layout_value_input(input_bytes, input, limits, match requested {",
                  "None => None, Some(requested) => Some(crate::options::decode_selection_view(requested))")),
                ("specs/decoder_input.rs", "part2_decode_layout_selected_value_input",
                 ("part2_decoder_execution_admission(input)", "part2_validate_selection(crate::codestream::selection_geometry_view(&input.size), requested)",
                  "part2_selected_layout_tiles(&input.size, input.parts, input.capabilities, selection.0,",
                  "[selection.1[0], selection.1[1], selection.1[2], selection.1[3]], selection.2, limits")),
                ("specs/decoder_input.rs", "part2_decode_typed_layout_value_input",
                 ("None => part2_decode_layout_input(input, limits)", "Some(requested) => part2_decode_layout_selected_value_input(input, requested, limits)",
                  "let discard_levels = match requested { None => 0u8, Some(selection) => selection.2 }",
                  "part2_typed_layout_input(input, decoded, discard_levels, limits)", "part1_validate_typed_output_shape(input_bytes, input.parts.len() as usize, input.size.components, image)")),
            ):
                actual = _coverage_spec_function_body(source_text((ROOT / path).resolve()), name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole raw container color Results require complete source/selection/value/header/color/target models")
        if entry["id"] in (_RAW_CONTAINER_IMAGE_ENTRY, _RAW_CONTAINER_COLOR_ENTRY):
            path = (ROOT / "src/decode/api.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "validate_jp2_display_profile"))
            model = _coverage_spec_function_body(source_text((ROOT / "specs/jp2_inspection.rs").resolve()), "part2_validate_jp2_display_profile")
            for actual, required in (
                (body, ("let count = file.codestream_count()", "!file.file_type().is_compatible_with(jp2::BoxType::JP2_BRAND)",
                        "count == 0", "file.file_type().is_jpx_compatible() && count != 1",
                        "DecodeError::malformed(0, MalformedKind::InvalidProfile)", "Ok(())")),
                (model, ("!part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JP2_BRAND)",
                         "file.streams.len() == 0", "part2_file_type_jpx(file.file_type) && file.streams.len() != 1",
                         "part2_container_error(0, crate::MalformedKind::InvalidProfile)", "Ok(())")),
            ):
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole raw container image/color Results require actual JP2 display profile admission")
        if entry["id"] == _RAW_CONTAINER_IMAGE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_RAW_CONTAINER_IMAGE_CONTRACTS) - _RAW_CONTAINER_IMAGE_APIS:
                raise ValueError("whole raw container image Results require actual inspection/core/output producer contracts")
            if not _RAW_CONTAINER_IMAGE_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _RAW_CONTAINER_IMAGE_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}) \
                    or not _RAW_CONTAINER_IMAGE_TESTS.issubset({(ref["path"], ref["symbol"]) for ref in entry["test_refs"]}):
                raise ValueError("whole raw container image Results require all public boundaries/raw/header/reference/selection/test bridges")
            path = (ROOT / "src/decode/api.rs").resolve()
            for name, selected, jph in (
                ("decode_jp2", False, False), ("decode_jp2_selected", True, False),
                ("decode_jph", False, True), ("decode_jph_selected", True, True),
            ):
                body = _coverage_function_body(source_text(path), function_header(path, name))
                required = [
                    ("jp2::inspect_jph" if jph else "jp2::parse_and_inspect_for_display") + "(input, options.limits())?",
                    "inspected.file().codestream_count() != 1" if jph else "validate_jp2_display_profile(inspected.file())?",
                    ("decode_codestream_selected" if selected else "decode_codestream")
                    + "(inspected.file().codestream(0)?.data(), options" + (", selection" if selected else "") + ")?",
                    "apply_jp2_output(decoded, inspected.file().header(), options.limits())",
                    "jp2::raw_render_file_known(jp2::raw_inspected_file_reference(&inspected))",
                ]
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw container image Results require actual raw/brand/count/selection/header handoffs")
            model = source_text((ROOT / "specs/container_images.rs").resolve())
            actual = _coverage_spec_function_body(model, "part2_decode_raw_single_container")
            required = (
                "if jph { part2_inspect_jph_container(input, limits) }",
                "else { part2_parse_and_inspect_container_mode(input, limits, true) }",
                "!jph && part2_validate_jp2_display_profile(file).is_err()",
                "jph && file.streams.len() != 1", "part2_container_error(0, crate::MalformedKind::InvalidProfile)",
                "part2_decode_raw_codestream(file.streams[0].1, limits, selection)",
                "part2_apply_output_header(decoded, part2_raw_associated_header(file.header).0,",
                "crate::limits::resource_component_limit(limits)", "crate::limits::resource_decoded_bytes_limit(limits)",
            )
            if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                raise ValueError("whole raw container image Results require complete raw/inspection/profile/selection/output models")
        if entry["id"] == _RAW_COMPOSITION_RENDER_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_RAW_COMPOSITION_RENDER_CONTRACTS) - _RAW_COMPOSITION_RENDER_APIS:
                raise ValueError("whole raw composition Result requires actual dimensions/layer/frame/canvas producer contracts")
            if not _RAW_COMPOSITION_RENDER_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _RAW_COMPOSITION_RENDER_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw composition Result requires proved public boundary and complete extent/source/getter/canvas bridges")
            path = (ROOT / "src/jpx/render.rs").resolve()
            for name, required in {
                "render_jpx_composition": ("jp2::parse_and_inspect(input, options.limits())?", "ensure_jpx(file)?",
                    "inspect_file(file, inspected.codestreams(), options.limits())?",
                    "if has_frames", "render_inspected_frame(file, &metadata, 0, options)",
                    "composition_dimensions(&metadata, options.limits())?", "decode_effective_layer(file, layer_index, options)?",
                    "target_width: metadata.layer(layer_index)?.width()", "target_height: metadata.layer(layer_index)?.height()",
                    "render_decoded_layers("),
                "composition_dimensions": ("layer.horizontal_offset()", "layer.vertical_offset()", "width = width.max(",
                    "height = height.max(", "Resource::Width", "Resource::Height", "Resource::Pixels"),
            }.items():
                body = _coverage_function_body(source_text(path), function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw composition Result requires actual timeline-first/fallback/source/extent/resource pipelines")
            model = source_text((ROOT / "specs/jpx_raw_composition.rs").resolve())
            for name, required in {
                "part2_render_raw_jpx_composition": ("part2_parse_and_inspect_container(input, limits)",
                    "part2_ensure_raw_jpx(inspected.0.file_type)", "part2_inspect_jpx_file(", "part2_render_source_composition("),
                "part2_render_source_composition": ("composition.source.3.len() > 0", "part2_render_inspected_source_frame(",
                    "part2_composition_dimensions(metadata, limits)", "part2_composition_source_prefix(", "part2_render_layers("),
                "part2_composition_source_prefix": ("part2_decode_effective_layer(file, layers, index, limits)",
                    "index >= metadata.layers.len()", "metadata.layers[index as int].geometry.0",
                    "metadata.layers[index as int].geometry.1", "previous.push((owned"),
                "part2_composition_extent_prefix": ("layer.offset.0 as nat + layer.geometry.0 as nat",
                    "layer.offset.1 as nat + layer.geometry.1 as nat", "width > u32::MAX as nat", "height > u32::MAX as nat"),
                "part2_composition_dimensions": ("metadata.composition", "width == 0 || height == 0",
                    "crate::Resource::Width", "crate::Resource::Height", "crate::Resource::Pixels", "u64::MAX as nat"),
            }.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole raw composition Result requires complete raw/timeline/fallback/extent/resource models")
        if entry["id"] == _RAW_RENDER_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_RAW_RENDER_CONTRACTS) - _RAW_RENDER_APIS:
                raise ValueError("whole public raw rendering Results require actual layer/image/frame producer contracts")
            if not _RAW_RENDER_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _RAW_RENDER_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole public raw rendering Results require both proved APIs and complete raw/source/render bridges")
            path = (ROOT / "src/jpx/render.rs").resolve()
            for name, required in {
                "render_jpx_layer": ("jp2::parse_and_inspect(input, options.limits())?", "ensure_jpx(inspected.file())?",
                    "decode_effective_layer(inspected.file(), layer_index, options)?.into_image()"),
                "render_jpx_frame": ("jp2::parse_and_inspect(input, options.limits())?", "ensure_jpx(file)?",
                    "inspect_file(file, inspected.codestreams(), options.limits())?",
                    "render_inspected_frame(file, &metadata, frame_index, options)"),
            }.items():
                body = _coverage_function_body(source_text(path), function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole public raw rendering Results require actual raw/admission/source/image/frame pipelines")
            model = source_text((ROOT / "specs/jpx_raw_frame.rs").resolve())
            for name, required in {
                "part2_render_raw_jpx_layer": ("part2_parse_and_inspect_container(input, limits)", "part2_ensure_raw_jpx(",
                    "part2_decode_effective_layer(", "part2_owned_layer_image(owned)"),
                "part2_render_raw_jpx_frame": ("part2_parse_and_inspect_container(input, limits)", "part2_inspect_jpx_file(",
                    "part2_render_inspected_source_frame(", "Some(value.source)"),
                "part2_raw_associated_header": ("header.palette", "header.mappings[i].component",
                    "header.mappings[i].mapping_type", "header.definitions", "header.image, header.color.0"),
                "part2_raw_layer_routing": ("layer.colors[0].0", "layer.registrations", "layer.definitions",
                    "layer.opacity", "layer.header.1"),
            }.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole public raw rendering Results require complete byte-derived header/source/routing/render models")
        if entry["id"] == _RAW_JPX_INSPECTION_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_RAW_JPX_INSPECTION_CONTRACTS) - _RAW_JPX_INSPECTION_APIS:
                raise ValueError("whole raw public JPX Result requires its actual checked inspector producer")
            if not _RAW_JPX_INSPECTION_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _RAW_JPX_INSPECTION_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw public JPX Result requires the proved public boundary and full raw/timeline/getter bridges")
            path = (ROOT / "src/jpx/inspection.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "inspect_jpx_layers"))
            required = ("jp2::parse_and_inspect(input, limits)?", "ensure_jpx(inspected.file())?",
                "inspect_file(inspected.file(), inspected.codestreams(), limits)")
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                raise ValueError("whole raw public JPX Result requires the actual raw/profile/inspector pipeline")
            model = source_text((ROOT / "specs/jpx_raw_inspection.rs").resolve())
            for name, required in {
                "part2_inspect_raw_jpx_layers": ("part2_parse_and_inspect_container(input, limits)",
                    "part2_ensure_raw_jpx(inspected.0.file_type)", "part2_inspect_jpx_file(part2_raw_inspection_file(inspected.0)"),
                "part2_raw_inspection_file": ("codestreams: file.streams.len() as usize",
                    "metadata: (file.metadata_boxes, file.metadata_depth)", "part2_raw_inspection_composition(value)"),
                "part2_raw_timeline_sets": ("sets[i].1", "part2_raw_timeline_instruction(sets[i].3[j])"),
                "part2_raw_timeline_instruction": ("value.source_x, value.source_y, value.source_width, value.source_height",
                    "value.persistent, value.next_reuse", "value.life"),
            }.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole raw public JPX Result requires full raw-source/metadata/instruction/timeline models")
        if entry["id"] == _RAW_INSPECTED_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_RAW_INSPECTED_CONTRACTS):
                raise ValueError("whole raw inspected Results require actual parser/JPH/profile contracts")
            if not _RAW_INSPECTED_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _RAW_INSPECTED_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw inspected Results require complete file/info/profile/getter bridges")
            path = (ROOT / "src/jp2/container.rs").resolve()
            for name, required in {
                "parse_and_inspect": ("parse_and_inspect_mode(input, limits, false)",),
                "parse_and_inspect_for_display": ("parse_and_inspect_mode(input, limits, true)",),
                "inspection_count": ("let count = file.codestream_count()", "if display_first",
                    "file.file_type().is_compatible_with(BoxType::JP2_BRAND)",
                    "!file.file_type().is_jpx_compatible()", "!file.file_type().is_jph_compatible()", "count.min(1)"),
                "parse_and_inspect_mode": ("parse(input, limits)?", "inspection_count(&file, display_first)",
                    "codestream::parse(codestream_box.data, limits)?",
                    "jph != info.profile.is_part15()", "Some(association) => association.parsed.as_ref()",
                    "None if index == 0 => Some(&file.header)", "validate_container_codestream(header, &info, codestream_box.header.offset())?",
                    "inspected_codestreams.push(info)", "InspectedJp2 { file, codestreams: inspected_codestreams, }"),
                "inspect_jph": ("parse_and_inspect(input, limits)?", "!inspected.file.file_type.is_jph_compatible()"),
            }.items():
                body = _coverage_function_body(source_text(path), function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw inspected Results require actual source/info/profile/header/default/output handoffs")
            model = source_text((ROOT / "specs/jp2_inspection.rs").resolve())
            for name, required in {
                "part2_inspected_header": ("part1_profile_optional_advertises_ht(info.1.2)", "Some(association) => association.2",
                    "index == 0", "part2_validate_selected_header(header.image"),
                "part2_inspection_count": ("if display_first && part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JP2_BRAND)",
                    "!part2_file_type_jpx(file.file_type)",
                    "!part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JPH_BRAND)",
                    "if file.streams.len() > 0 { 1 } else { 0 }", "else { file.streams.len() }"),
                "part2_inspected_codestreams": ("index >= part2_inspection_count(file, display_first)",
                    "part1_parse_info(file.streams[index as int].1, limits)",
                    "part2_inspected_header(file, index, info)", "infos.push(info)"),
                "part2_parse_and_inspect_container": ("part2_parse_and_inspect_container_mode(input, limits, false)",),
                "part2_parse_and_inspect_container_mode": ("part2_parse_container(input, *limits)",
                    "part2_inspected_codestreams(file, limits, 0, Seq::empty(), display_first)"),
                "part2_inspect_jph_container": ("part2_parse_and_inspect_container(input, limits)",
                    "part2_file_type_compatible(inspected.0.file_type, crate::jp2::BoxType::JPH_BRAND)"),
            }.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole raw inspected Results require complete raw producer/profile/default/info/JPH models")
        if entry["id"] == _RAW_CONTAINER_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_RAW_CONTAINER_CONTRACTS):
                raise ValueError("whole raw container Result requires the actual complete parser contract")
            if not _RAW_CONTAINER_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _RAW_CONTAINER_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw container Result requires full traversal/owner/output/attachment bridges")
            path = (ROOT / "src/jp2/container.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "parse"))
            required = (
                "box_reader_from_input(input, limits)?", "required_box(&mut reader, 0)?",
                "box_type.equals(BoxType::SIGNATURE) || box_type.equals(BoxType::FILE_TYPE)",
                "parse_jp2_header_profile(", "file_type.is_jph_compatible()",
                "parse_codestream_header(", "parse_compositing_layer(box_ref, limits)?",
                "parse_composition(box_ref, limits)?", "inspect_metadata_box(box_ref, limits, 1, u32::MAX - 1)?",
                "let mut box_count = 2_u64", "metadata_depth = metadata_depth.max(depth)",
                "super::clone_support::codestream_association_clone(", ".get_mut(header_index)",
                "codestream_box.codestream_header = Some(association)",
                "!codestream_headers.is_empty() && codestream_headers.len() != codestream_boxes.len()",
                "validate_layer_references(&compositing_layers, codestream_boxes.len())?",
                "Jp2File { file_type, header, codestreams: codestream_boxes, compositing_layers, composition, metadata_boxes, metadata_depth, box_count, }",
            )
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                raise ValueError("whole raw container Result requires actual source producers/counters/owned attachment/output handoffs")
            model = source_text((ROOT / "specs/jp2_container.rs").resolve())
            for name, required in {
                "part2_container_step": ("previous.box_count == u64::MAX", "part2_parse_jp2_header_profile(",
                    "part2_file_type_compatible(file_type, crate::jp2::BoxType::JPH_BRAND)",
                    "part2_parse_codestream_header(",
                    "kind == crate::jp2::BoxType::SIGNATURE || kind == crate::jp2::BoxType::FILE_TYPE",
                    "part2_parse_compositing_layer(", "part2_parse_composition(", "part2_inspect_metadata_box(",
                    "metadata_depth: if state.metadata_depth < value.1 { value.1 } else { state.metadata_depth }"),
                "part2_container_attach": ("streams[i].0, streams[i].1", "Some(part2_codestream_association_clone(associations[i]))"),
                "part2_container_finish": ("state.associations.len() != 0 && state.associations.len() != state.streams.len()", "part2_validate_layer_references(",
                    "streams: part2_container_attach(", "metadata_depth: state.metadata_depth", "box_count: state.box_count"),
                "part2_parse_container": ("part2_container_prologue(input, limits)", "part2_container_initial_state()"),
            }.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole raw container Result requires complete raw traversal/metadata/attachment/final output models")
        if entry["id"] == _RAW_COMPOSITION_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_RAW_COMPOSITION_CONTRACTS):
                raise ValueError("whole raw composition Results require actual cursor/dimension/instruction/composition/reference contracts")
            if not _RAW_COMPOSITION_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _RAW_COMPOSITION_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw composition Results require full source/cursor/record/output/reference bridges")
            path = (ROOT / "src/jp2/composition.rs").resolve()
            for name, required in {
                "has_explicit_registration": (
                    "found = found || !layers[index].registrations.is_empty()", "index += 1",
                ),
                "read_u32_at": ("position.checked_add(4)", "input.get(*position..end)", "*position = end"),
                "validate_dimensions": ("width == 0 || height == 0", "width > limits.maximum_width()", "height > limits.maximum_height()", "pixels > limits.maximum_pixels()"),
                "parse_instruction_set": (
                    "flags & !0x0027 != 0", "have_source_region = flags & 32 != 0",
                    "persistent = encoded_life & 0x8000_0000 != 0", "life_value = encoded_life & 0x7fff_ffff",
                    "life_value.checked_mul(tick)", "source_height = read_u32_at(box_ref.payload, &mut cursor, offset)?",
                    "instructions.push(CompositionInstruction { target_x, target_y, target_width, target_height, life, persistent, next_reuse, source_x, source_y, source_width, source_height, })",
                ),
                "parse_composition": (
                    "box_reader_from_input(box_ref.payload, limits)?", "options.is_some() || !instruction_sets.is_empty()",
                    "validate_dimensions(width, height, limits, base_offset)?", "parse_instruction_set(",
                    "actual as u64 > u64::from(limits.maximum_layers())", "encoded_loop_count == u8::MAX", "has_unknown_boxes = true",
                ),
                "validate_layer_references": (
                    "has_explicit_registration(layers)", "explicit_registration || layer_index >= codestream_count",
                    "usize::from(registration.codestream_index) >= codestream_count", "layer.header.offset()",
                ),
            }.items():
                body = _coverage_function_body(source_text(path), function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw composition Results require actual cursor/record/geometry/loop/reference handoffs")
            model = source_text((ROOT / "specs/jp2_composition.rs").resolve())
            for name, required in {
                "part2_read_composition_word": ("end > usize::MAX as nat", "end > input.len()", "end as usize"),
                "part2_instruction_record": (
                    "source_width == 0 || source_height == 0", "if flags & 4 != 0 { encoded_life & 0x7fff_ffffu32 } else { 0u32 }",
                    "life_value as nat * tick as nat", "life > u32::MAX as nat",
                ),
                "part2_parse_instruction_set": ("flags & !0x0027u16 != 0", "remaining % bytes != 0", "resource_work_limit(limits)"),
                "part2_composition_finish": ("value.2 == u8::MAX", "(value.2 + 1) as u8"),
            }.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole raw composition Results require complete cursor/flags/record/life/loop models")
        if entry["id"] == _RAW_LAYER_HEADER_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_RAW_LAYER_HEADER_CONTRACTS):
                raise ValueError("whole raw layer Results require actual registration/color/opacity/borrowed layer contracts")
            if not _RAW_LAYER_HEADER_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _RAW_LAYER_HEADER_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw layer Results require complete ordered metadata/registration/borrow bridges")
            path = (ROOT / "src/jp2/composition.rs").resolve()
            for name, required in {
                "parse_codestream_registration": (
                    "horizontal_grid_size == 0 || vertical_grid_size == 0", "count as u64 > u64::from(limits.maximum_codestreams())",
                    "horizontal_subsampling == 0", "vertical_subsampling == 0",
                    "u16::from(horizontal_offset) >= horizontal_grid_size", "u16::from(vertical_offset) >= vertical_grid_size",
                    "position.checked_add(6)",
                ),
                "parse_color_group": (
                    "box_reader_from_input(box_ref.payload, limits)?", "colors.push(parse_color_specification(child, base_offset)?)",
                    "colors.len() as u64 > u64::from(limits.maximum_components())",
                ),
                "parse_layer_opacity": (
                    "add_offset(base_offset, box_ref.header.offset())?", "let channels = box_ref.payload[1]",
                    "copy_bytes(&box_ref.payload[2..])?", "channels == 0",
                ),
                "parse_compositing_layer": (
                    "box_reader_from_input(box_ref.payload, limits)?", "parse_codestream_registration(child, base_offset, limits)?",
                    "opacity.is_some() || !channel_definition_records.is_empty()", "parse_channel_definition(child, u16::MAX, base_offset)?",
                    "inspect_metadata_box(child, limits, 1, u32::MAX - 1)?",
                    "header: box_ref.header", "payload: box_ref.payload",
                ),
            }.items():
                body = _coverage_function_body(source_text(path), function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw layer Results require actual source registration/ICC/key/borrow/metadata handoffs")
            model = source_text((ROOT / "specs/jp2_layer.rs").resolve())
            for name, required in {
                "part2_parse_codestream_registration": ("horizontal == 0 || vertical == 0", "resource_codestream_limit(limits)",),
                "part2_registration_entry": ("horizontal_offset as u16 >= horizontal", "vertical_offset as u16 >= vertical"),
                "part2_parse_layer_opacity": ("part2_box_add_offset(base, input.0.1)", "payload.subrange(2, payload.len() as int)", "channels: payload[1]"),
                "part2_color_group_boxes": ("colors.push(value)", "resource_component_limit(&limits)", "part2_parse_color_specification(input, base)"),
                "part2_parse_compositing_layer": ("header: input.0, payload: input.1", "has_registration: false"),
                "part2_raw_layer_step": ("part2_inspect_metadata_box(input, limits, 1, (u32::MAX - 1) as u32)", "layer.opacity.is_some() || layer.definitions.len() > 0"),
            }.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole raw layer Results require full registration/ICC/key/borrow/order models")
        if entry["id"] == _METADATA_TREE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_METADATA_TREE_CONTRACTS):
                raise ValueError("whole raw metadata tree Result requires actual recursive native producer contract")
            if not _METADATA_TREE_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _METADATA_TREE_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw metadata tree Result requires full count/depth/reader-seed bridges")
            path = (ROOT / "src/jp2/metadata.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "inspect_metadata_box"))
            required = (
                "depth > limits.maximum_box_depth()", "return Ok((1, depth))",
                "box_reader_from_input(box_ref.payload, limits)?", "remaining_boxes == 0", "remaining_boxes -= 1",
                "remaining_depth.checked_sub(1)",
                "inspect_metadata_box(child, limits, child_depth, child_remaining)?",
                "immediate_children.checked_add(1)", "if immediate_children < 2 { return Err",
                "count > u32::MAX - child_count", "crate::refinement::metadata_count(count, child_count)",
                "u64::from(count) > limits.maximum_work_units()", "maximum_depth.max(observed_depth)",
            )
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                raise ValueError("whole raw metadata tree Result requires actual ordered reader/child/count/depth handoffs")
            model = source_text((ROOT / "specs/jp2_metadata.rs").resolve())
            for name, required in {
                "part2_inspect_metadata_box": (
                    "depth > crate::limits::resource_box_depth_limit(&limits)",
                    "input.0.0 != crate::jp2::BoxType::ASSOCIATION", "Ok((1, depth))",
                    "part2_box_reader_from_input(input.1, limits)",
                ),
                "part2_metadata_children": (
                    "None => if immediate < 2", "immediate == usize::MAX", "(immediate + 1) as usize",
                    "part2_box_reader_next_ref(reader)", "fuel == 0", "remaining == 0",
                    "part2_inspect_metadata_box(child, limits, child_depth, (remaining - 1) as u32)",
                    "count > u32::MAX - observed.0", "part2_metadata_count(count, observed.0)",
                    "if maximum >= observed.1 { maximum } else { observed.1 }",
                ),
            }.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole raw metadata tree Result requires complete recursive reader/error/count/depth models")
        if entry["id"] == _ASSOCIATION_CLONE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_ASSOCIATION_CLONE_CONTRACTS):
                raise ValueError("whole association clone Results require both actual clone producer contracts")
            if not _ASSOCIATION_CLONE_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _ASSOCIATION_CLONE_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole association clone Results require full optional header and borrowed payload bridges")
            path = (ROOT / "src/jp2/clone_support.rs").resolve()
            for name, required in {
                "optional_jp2_header_clone": ("None => None", "Some(header) => Some(jp2_header_clone(header))"),
                "codestream_association_clone": (
                    "header: Clone::clone(&source.header)", "payload: Clone::clone(&source.payload)",
                    "parsed: optional_jp2_header_clone(&source.parsed)",
                ),
            }.items():
                body = _coverage_function_body(source_text(path), function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole association clone Results require actual original field clone and optional header routing bodies")
            model = source_text((ROOT / "specs/jp2_associated_header.rs").resolve())
            for _, name in _ASSOCIATION_CLONE_MODELS:
                if (_coverage_spec_function_body(model, name) or "").strip() != "value":
                    raise ValueError("whole association clone Results require complete unchanged metadata identity models")
        if entry["id"] == _OWNED_HEADER_CLONE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_OWNED_HEADER_CLONE_CONTRACTS):
                raise ValueError("whole owned header clone Results require all four actual clone producer contracts")
            if not _OWNED_HEADER_CLONE_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _OWNED_HEADER_CLONE_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole owned header clone Results require complete profile/palette/header metadata bridges")
            path = (ROOT / "src/jp2/clone_support.rs").resolve()
            for name, required in {
                "color_specification_clone": (
                    "method: Clone::clone(&source.method)", "precedence: Clone::clone(&source.precedence)",
                    "approximation: Clone::clone(&source.approximation)", "icc_profile: Clone::clone(&source.icc_profile)",
                ),
                "palette_clone": (
                    "entries: Clone::clone(&source.entries)", "columns: Clone::clone(&source.columns)", "values: Clone::clone(&source.values)",
                ),
                "optional_palette_clone": ("None => None", "Some(palette) => Some(palette_clone(palette))"),
                "jp2_header_clone": (
                    "color: color_specification_clone(&source.color)", "palette: optional_palette_clone(&source.palette)",
                    "component_mappings: Clone::clone(&source.component_mappings)",
                    "channel_definition_records: Clone::clone(&source.channel_definition_records)",
                ),
            }.items():
                body = _coverage_function_body(source_text(path), function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole owned header clone Results require actual original field clone and optional routing bodies")
            model = source_text((ROOT / "specs/jp2_associated_header.rs").resolve())
            for _, name in _OWNED_HEADER_CLONE_MODELS:
                if (_coverage_spec_function_body(model, name) or "").strip() != "value":
                    raise ValueError("whole owned header clone Results require complete unchanged metadata identity models")
        if entry["id"] == _ASSOCIATED_HEADER_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_ASSOCIATED_HEADER_CONTRACTS):
                raise ValueError("whole associated-header Result requires actual complete native parser contract")
            if not _ASSOCIATED_HEADER_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _ASSOCIATED_HEADER_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole associated-header Result requires actual full/default-clone/override metadata bridges")
            path = (ROOT / "src/jp2/headers.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "parse_codestream_header"))
            required = (
                "if let Ok(header) = parse_jp2_header(payload, limits, base_offset)",
                "super::clone_support::jp2_header_clone(default_header)", "box_reader_from_input(payload, limits)?",
                "header.palette = None", "header.component_mappings.clear()", "header.channel_definition_records.clear()",
                "palette_override || mapping_override || definition_override", "mapping_override || definition_override",
                "if resolution_override", "if image_override && matches!(header.image.bit_depth, ComponentBitDepth::Variable) != saw_bpcc",
                "header.nested_box_count = nested_box_count",
                "if crate::refinement::first_override_allowed(color_override) { header.color = parse_color_specification(box_ref, base_offset)?; color_override = true; } else { validate_color_specification_prefix(box_ref, base_offset)?; }",
            )
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                raise ValueError("whole associated-header Result requires actual clone/clear/order/retained metadata handoffs")
            model = source_text((ROOT / "specs/jp2_associated_header.rs").resolve())
            for name, required in {
                "part2_parse_codestream_header": (
                    "part2_parse_jp2_header(payload, limits, base)", "None => Err(part2_raw_header_missing(base))",
                    "part2_associated_header_boxes(payload, reader, Part2AssociatedHeaderState",
                ),
                "part2_associated_header_step": (
                    "image, palette: None, mappings: Seq::empty(), definitions: Seq::empty()",
                    "state.palette_override || state.mapping_override || state.definition_override",
                    "part2_parse_color_specification(input, base)", "!state.color_override",
                    "part2_validate_color_specification_prefix(input, base)",
                ),
                "part2_associated_header_finish": (
                    "state.image_override", "state.header.palette.is_some() && state.header.mappings.len() == 0",
                    "nested_box_count: state.nested, ..state.header",
                ),
            }.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole associated-header Result requires complete inherited/override/output models")
        if entry["id"] == _RAW_JP2_HEADER_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_RAW_JP2_HEADER_CONTRACTS):
                raise ValueError("whole raw JP2 header Result requires actual complete assembler contract")
            if not _RAW_JP2_HEADER_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _RAW_JP2_HEADER_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}) \
                    or not _RAW_JP2_HEADER_TESTS.issubset({(ref["path"], ref["symbol"]) for ref in entry["test_refs"]}):
                raise ValueError("whole raw JP2 header Result requires every raw producer and complete owned metadata bridge")
            path = (ROOT / "src/jp2/headers.rs").resolve()
            text = source_text(path)
            strict = _coverage_function_body(text, function_header(path, "parse_jp2_header"))
            if strict is None or "parse_jp2_header_profile(payload,limits,base_offset,false)" not in "".join(strict.split()):
                raise ValueError("whole raw JP2 header Result requires strict JP2 forwarding without unspecified-colour admission")
            absent = _coverage_function_body(text, function_header(path, "unspecified_jph_color"))
            if absent is None or any("".join(item.split()) not in "".join(absent.split()) for item in (
                "definitions[index].definition.channel_type()", "ChannelType::Color", "MalformedKind::InvalidProfile",
                "method: ColorMethod::Unspecified", "precedence: 0", "approximation: 0", "icc_profile: None",
            )):
                raise ValueError("whole raw JP2 header Result requires actual explicit-absence construction and colour-channel exclusion")
            body = _coverage_function_body(text, function_header(path, "parse_jp2_header_profile"))
            required = (
                "box_reader_from_input(payload, limits)?", "required_box(&mut reader, 0)",
                "parse_image_header(image_box, limits, base_offset)?",
                "reader.position <= previous_position || reader.position > payload.len()",
                "parse_color_specification(box_ref, base_offset)?", "if color.is_none()",
                "if color.is_none() { color = Some(parse_color_specification(box_ref, base_offset)?); } else { validate_color_specification_prefix(box_ref, base_offset)?; }",
                "parse_palette(box_ref, base_offset)?", "validate_bpcc(box_ref, image, base_offset)?",
                "parse_component_mapping(box_ref, image.components, palette_columns, limits, base_offset,)",
                "parse_channel_definition(box_ref, output_channels, base_offset)?",
                "None if allow_unspecified && image.unknown_color_space",
                "unspecified_jph_color(&channel_definition_records, base_offset)?",
                "let (capture, display) = parse_resolution_superbox(",
                "Ok(Jp2Header { image, color, nested_box_count, palette_entries, palette_columns, component_mapping_entries, channel_definitions, palette, component_mappings, channel_definition_records, capture_resolution, display_resolution, })",
            )
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required) \
                    or body.count("u16::try_from(component_mappings.len())") != 2:
                raise ValueError("whole raw JP2 header Result requires actual full fields/ordered producer/count handoffs")
            if body.index("let (capture, display) = parse_resolution_superbox(") > body.index("if capture_resolution.is_some()"):
                raise ValueError("whole raw JP2 header Result requires native resolution-parse-before-duplicate priority")
            model = source_text((ROOT / "specs/jp2_header.rs").resolve())
            for name, required in {
                "part2_parse_jp2_header": (
                    "part2_parse_jp2_header_profile(payload, limits, base, false)",
                ),
                "part2_parse_jp2_header_profile": (
                    "part2_box_reader_from_input(payload, limits)", "part2_box_reader_required(reader, 0)",
                    "part2_parse_image_header(input, &limits, base)",
                ),
                "part2_raw_header_boxes": (
                    "next.1.position <= reader.position || next.1.position > payload.len()",
                    "state.nested == u32::MAX", "nested: (state.nested + 1) as u32",
                    "part2_raw_header_finish(state, base, allow_unspecified)",
                ),
                "part2_raw_header_step": (
                    "part2_parse_color_specification(input, base)", "state.color.is_none()",
                    "part2_validate_color_specification_prefix(input, base)",
                    "part2_parse_palette(input, base)", "part2_parse_component_mapping(",
                    "part2_parse_channel_definition(", "part2_parse_resolution_superbox(input.1, limits, nested_base)",
                ),
                "part2_raw_header_finish": (
                    "allow_unspecified && state.image.unknown_color_space",
                    "part2_unspecified_jph_color(state.definitions, base)",
                    "state.palette.is_some() && state.mappings.len() == 0",
                    "component_mapping_entries: state.mappings.len() as u16",
                    "channel_definitions: state.definitions.len() as u16",
                    "palette: state.palette, mappings: state.mappings, definitions: state.definitions",
                ),
                "part2_unspecified_jph_color": (
                    "definitions[i].1.0 == crate::ChannelType::Color", "crate::MalformedKind::InvalidProfile",
                    "Ok((crate::jp2::ColorMethod::Unspecified, 0, 0, None))",
                ),
            }.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole raw JP2 header Result requires complete raw producer/count/output models")
        if entry["id"] == _PALETTE_RESULT_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_PALETTE_RESULT_CONTRACTS):
                raise ValueError("whole raw owned Palette Result requires actual complete parser contract")
            if not _PALETTE_RESULT_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _PALETTE_RESULT_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}) \
                    or not _PALETTE_RESULT_TESTS.issubset({(ref["path"], ref["symbol"]) for ref in entry["test_refs"]}):
                raise ValueError("whole raw owned Palette Result requires full descriptor/row/owner/error bridges")
            path = (ROOT / "src/jp2/color.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "parse_palette"))
            required = (
                "entries == 0 || entries > 1024 || columns == 0", "descriptor_end > box_ref.payload.len()",
                "let mut columns = Vec::with_capacity(usize::from(columns))",
                "parse_bit_depth(box_ref.payload[descriptor], base_offset)?",
                "let mut values = Vec::with_capacity(value_count)",
                "values.push(parse_palette_value(&box_ref.payload[offset..end], descriptor.precision, descriptor.signed, base_offset,)?)",
                "column = column.checked_add(1)", "entry = entry.checked_add(1)",
                "offset != box_ref.payload.len() || values.len() != value_count",
                "Ok(Palette { entries, columns, values, })",
            )
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                raise ValueError("whole raw owned Palette Result requires actual native owners/fields/ordered byte producers")
            model = source_text((ROOT / "specs/jp2_palette.rs").resolve())
            for name, required in {
                "part2_parse_palette": (
                    "entries == 0 || entries > 1024 || count == 0", "part2_palette_descriptors(input, base, count)",
                    "payload.len() != expected", "part2_palette_rows(input, base, descriptors.0, entries as nat)",
                    "values.1 != payload.len() || values.0.len() != value_count", "Ok((entries, descriptors.0, values.0))",
                ),
                "part2_palette_descriptor_step": (
                    "part2_container_bit_depth(input.1[3 + index as int], base)",
                    "previous.0.push(crate::jp2::PaletteColumn { precision: bits, signed })",
                ),
                "part2_palette_value_step": (
                    "columns[index as int]", "input.1.subrange(previous.1 as int, end as int)",
                    "descriptor.precision, descriptor.signed, base",
                ),
                "part2_palette_rows": (
                    "part2_palette_rows(input, base, columns, (count - 1) as nat)",
                    "part2_palette_row(input, base, columns, initial, columns.len())",
                ),
            }.items():
                body = _coverage_spec_function_body(model, name)
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw owned Palette Result requires complete ordered descriptor/row/output models")
        if entry["id"] == _PALETTE_VALUE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_PALETTE_VALUE_CONTRACTS):
                raise ValueError("whole raw palette scalar Result requires actual value producer contract")
            if not _PALETTE_VALUE_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _PALETTE_VALUE_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw palette scalar Result requires full byte/modulus/error folds")
            path = (ROOT / "src/jp2/color.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "parse_palette_value"))
            required = (
                "precision == 0 || precision > 38 || bytes.is_empty() || bytes.len() > 5",
                "raw.checked_mul(256)", "value.checked_add(u64::from(bytes[index]))",
                "modulus.checked_mul(2)", "modulus.checked_sub(1)", "let value = raw & mask",
                "signed && value & (modulus >> 1) != 0", "modulus.checked_sub(value)", "i64::try_from(value)",
            )
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                raise ValueError("whole raw palette scalar Result requires actual admission/byte/mask/sign handoffs")
            model = source_text((ROOT / "specs/jp2_palette.rs").resolve())
            for name, required in {
                "part2_parse_palette_value": (
                    "precision == 0 || precision > 38 || bytes.len() == 0 || bytes.len() > 5",
                    "raw & ((modulus - 1) as u64)", "signed && value & (modulus >> 1u64) != 0",
                    "value > modulus || modulus as int - value as int > i64::MAX as int",
                ),
                "part2_palette_word_prefix": ("raw as nat * 256 + bytes[count - 1] as nat",),
                "part2_palette_modulus_prefix": ("value as nat * 2",),
            }.items():
                body = _coverage_spec_function_body(model, name)
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw palette scalar Result requires complete byte/modulus/sign/error models")
        if entry["id"] == _RESOLUTION_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_RESOLUTION_CONTRACTS):
                raise ValueError("whole raw resolution Results require actual primitive/superbox/copy contracts")
            if not _RESOLUTION_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _RESOLUTION_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw resolution Results require full byte/traversal/copy bridges")
            path = (ROOT / "src/jp2/metadata.rs").resolve()
            for name, required in {
                "parse_resolution": (
                    "box_ref.payload.len() != 10",
                    "vertical_numerator == 0 || vertical_denominator == 0 || horizontal_numerator == 0 || horizontal_denominator == 0",
                    "vertical_exponent: box_ref.payload[8] as i8", "horizontal_exponent: box_ref.payload[9] as i8",
                ),
                "parse_resolution_superbox": (
                    "box_reader_from_input(payload, limits)?", "reader.next_box_ref()",
                    "reader.position <= previous_position || reader.position > payload.len()",
                    "capture.is_some()", "display.is_some()",
                    "capture = Some(parse_resolution(box_ref, base_offset)?)",
                    "display = Some(parse_resolution(box_ref, base_offset)?)",
                    "capture.is_none() && display.is_none()",
                ),
                "copy_bytes": ("input.get(index)", "index.checked_add(1)", "Ok(output)"),
            }.items():
                body = _coverage_function_body(source_text(path), function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw resolution Results require actual fields/traversal/copy handoffs")
                if name == "parse_resolution_superbox" and body.index("reader.position <= previous_position") > body.index("next.map_err"):
                    raise ValueError("whole raw resolution Results require native progress-before-reader-error priority")
            model = source_text((ROOT / "specs/jp2_resolution.rs").resolve())
            for name, required in {
                "part2_parse_resolution": (
                    "payload.len() != 10", "vertical_numerator == 0 || vertical_denominator == 0",
                    "horizontal_numerator == 0 || horizontal_denominator == 0",
                    "vertical_exponent: payload[8] as i8", "horizontal_exponent: payload[9] as i8",
                ),
                "part2_resolution_boxes": (
                    "part2_box_reader_next_ref(reader)", "next.1.position <= reader.position || next.1.position > payload.len()",
                    "Err(part2_resolution_progress_error(base, reader.position))", "capture.is_some()", "display.is_some()",
                    "part2_resolution_boxes(payload, next.1, base, Some(value), display)",
                    "part2_resolution_boxes(payload, next.1, base, capture, Some(value))",
                ),
                "part2_resolution_finish": ("capture.is_none() && display.is_none()", "Ok((capture, display))"),
                "part2_copy_metadata_bytes": ("Ok(input)",),
            }.items():
                body = _coverage_spec_function_body(model, name)
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw resolution Results require complete field/error/traversal/copy models")
        if entry["id"] == _CHANNEL_HEADER_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_CHANNEL_HEADER_CONTRACTS):
                raise ValueError("whole raw channel Results require actual mapping and definition contracts")
            if not _CHANNEL_HEADER_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _CHANNEL_HEADER_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw channel Results require full record/validity/error/constructor bridges")
            path = (ROOT / "src/jp2/color.rs").resolve()
            for name, required in {
                "parse_component_mapping": (
                    "box_ref.payload.is_empty() || !box_ref.payload.len().is_multiple_of(4)",
                    "u16::try_from(entry_count)", "entries > limits.maximum_components()",
                    "crate::refinement::component_mapping_valid(component, components, mapping_type, palette_column, palette_columns,)",
                    "mappings.push(ComponentMapping { component, mapping_type, })", "offset.checked_add(4)",
                ),
                "parse_channel_definition": (
                    "entries == 0 || box_ref.payload.len() != expected_length",
                    "crate::refinement::channel_definition_valid(channel, channel_type, association, output_channels,)",
                    "definition: crate::image::channel_definition_new(channel_type, association)", "offset.checked_add(6)",
                ),
            }.items():
                body = _coverage_function_body(source_text(path), function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw channel Results require actual ordered records and native validity handoffs")
            model = source_text((ROOT / "specs/jp2_channel_header.rs").resolve())
            for name, required in {
                "part2_parse_component_mapping": (
                    "length == 0 || length % 4 != 0", "count > u16::MAX as nat",
                    "count > crate::limits::resource_component_limit(limits)",
                ),
                "part2_mapping_entry": (
                    "offset + 4 > payload.len()", "part2_component_mapping_valid(component, components, kind, column, palette_columns)",
                    "crate::jp2::MappingType::Palette { column }",
                ),
                "part2_parse_channel_definition": ("entries == 0 || payload.len() != 2 + entries as nat * 6",),
                "part2_channel_record": (
                    "offset + 6 > payload.len()", "part2_channel_definition_valid(channel, kind, association, output_channels)",
                    "association == 0xffff", "crate::ChannelAssociation::Color(association)",
                ),
            }.items():
                body = _coverage_spec_function_body(model, name)
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw channel Results require complete length/admission/record models")
        if entry["id"] == _COLOR_HEADER_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_COLOR_HEADER_CONTRACTS):
                raise ValueError("whole raw color Result requires actual full color parser contract")
            if {("specs/jp2_color_header.rs", name) for name in (
                    "part2_parse_color_specification", "part2_validate_color_specification_prefix")} != {
                    (ref["path"], ref["symbol"]) for ref in entry["spec_refs"]} \
                    or not _COLOR_HEADER_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw color Result requires complete method/metadata/ICC-copy bridges")
            path = (ROOT / "src/jp2/color.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "parse_color_specification"))
            required = ("validate_color_specification_prefix(box_ref, base_offset)?", "method_value == 1", "box_ref.payload.len() != 7",
                        "method_value == 2", "method_value == 3", "copy_profile(&box_ref.payload[3..])?",
                        "precedence: box_ref.payload[1]", "approximation: box_ref.payload[2]", "icc_profile,")
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required) \
                    or "".join(body.split()).count("copy_profile(&box_ref.payload[3..])?") != 2:
                raise ValueError("whole raw color Result requires actual method/metadata/full-ICC handoffs")
            prefix = _coverage_function_body(source_text(path), function_header(path, "validate_color_specification_prefix"))
            prefix_required = ("box_ref.payload.len() < 3", "add_offset(base_offset, box_ref.header.offset())?",
                               "MalformedKind::InvalidBoxLength", "Ok(())")
            if prefix is None or any("".join(item.split()) not in "".join(prefix.split()) for item in prefix_required):
                raise ValueError("whole raw color Result requires actual common-prefix/error validation")
            model = source_text((ROOT / "specs/jp2_color_header.rs").resolve())
            prefix = _coverage_spec_function_body(model, "part2_validate_color_specification_prefix")
            if prefix is None or any("".join(item.split()) not in "".join(prefix.split()) for item in (
                    "input.1.len() < 3", "part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength)",
                    "Ok(())")):
                raise ValueError("whole raw color Result requires complete common-prefix/error model")
            actual = _coverage_spec_function_body(model, "part2_parse_color_specification")
            required = ("payload.len() < 3", "payload.len() != 7", "length == 0",
                        "payload[1], payload[2]", "Some(payload.subrange(3, payload.len() as int))",
                        "MalformedKind::InvalidColorSpecification")
            if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                raise ValueError("whole raw color Result requires complete lazy-error/metadata/ICC-byte model")
        if entry["id"] == _IMAGE_HEADER_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_IMAGE_HEADER_CONTRACTS):
                raise ValueError("whole raw image-header Result requires actual image/depth/BPCC contracts")
            if not _IMAGE_HEADER_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _IMAGE_HEADER_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw image-header Result requires complete raw field/lazy-offset/ordered-depth models")
            path = (ROOT / "src/jp2/headers.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "parse_image_header"))
            required = (
                "box_ref.payload.len() != 14", "width == 0 || height == 0 || components == 0 || box_ref.payload[11] != 7",
                "width > limits.maximum_width()", "height > limits.maximum_height()",
                "components > limits.maximum_components()", "pixels > limits.maximum_pixels()",
                "parse_bit_depth(box_ref.payload[10], base_offset)?", "match box_ref.payload[12]", "match box_ref.payload[13]",
            )
            normalized = "".join(body.split()) if body is not None else ""
            positions = [normalized.find("".join(item.split())) for item in required]
            if any(position < 0 for position in positions) or positions != sorted(positions):
                raise ValueError("whole raw image-header Result requires actual field/limit/precision/flag priority")
            model = source_text((ROOT / "specs/jp2_image_header.rs").resolve())
            handoffs = {
                "part2_container_bit_depth": ("value == 0xff", "bits > 38", "signed: value & 0x80 != 0"),
                "part2_image_box_error": ("part2_box_add_offset(base, header.1)",),
                "part2_parse_image_header": ("payload.len() != 14", "part2_container_bit_depth(payload[10], base)",
                    "unknown_color_space: payload[12] == 1", "intellectual_property: payload[13] == 1"),
                "part2_validate_bpcc": ("input.1.len() != image.components as nat", "part2_bpcc_prefix(input, base, input.1.len())"),
            }
            for name, fragments in handoffs.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in fragments):
                    raise ValueError("whole raw image-header Result requires complete exact depth/lazy-offset/field models")
        if entry["id"] == _FILE_TYPE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_FILE_TYPE_CONTRACTS):
                raise ValueError("whole raw file-type Result requires actual payload/profile contracts")
            if not _FILE_TYPE_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _FILE_TYPE_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw file-type Result requires all actual byte/brand/error/prefix bridges")
            path = (ROOT / "src/jp2/container.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "parse_file_type"))
            required = (
                "box_ref.header.payload_offset()?", "box_ref.payload.len() < 8",
                "if compatible_brand_count_u64 > u64::from(limits.maximum_compatible_brands())",
                "let brand = box_type_from_bytes(",
                "read_box_type_at(box_ref.payload, position, payload_offset)?",
                "if previous.equals(compatible)", "compatible_brands.push(compatible)",
                "minor_version: read_u32(",
            )
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                raise ValueError("whole raw file-type Result requires actual ordered byte/limit/duplicate/field handoffs")
            text = source_text(path)
            header = function_header(path, "parse")
            start = text.rfind("#[cfg_attr(verus_keep_ghost, verus_spec(", 0, header.start()) if header else -1
            contract = text[start:header.start()] if start >= 0 else ""
            if "super::container_prefix_relation(result,crate::specs::part2_container_prologue(input@,*limits))" \
                    not in "".join(contract.split()):
                raise ValueError("raw file-type prefix requires actual public parser error/type relation")
            body = _coverage_function_body(text, header)
            required = ("box_reader_from_input(input, limits)?", "required_box(&mut reader, 0)?",
                        "required_box(&mut reader, 1)?", "parse_file_type(file_type_box, limits)?",
                        "validate_file_type_profile(&file_type, file_type_box.header.offset())?")
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                raise ValueError("raw file-type prefix requires actual shared-reader/signature/payload/profile producers")
            model = source_text((ROOT / "specs/jp2_file_type.rs").resolve())
            handoffs = {
                "part2_parse_file_type": ("payload.len() < 8 || payload.len() % 4 != 0",
                    "count > maximum_brands as nat", "part2_file_type_brands_prefix(payload, offset, count)"),
                "part2_file_type_brands_prefix": ("previous.contains(brand)", "Ok(previous.push(brand))"),
                "part2_container_prologue": ("part2_box_reader_from_input(input, limits)",
                    "part2_box_reader_required(reader, 0)", "part2_box_reader_required(first.1, 1)",
                    "signature.1 != seq![0x0du8, 0x0au8, 0x87u8, 0x0au8]",
                    "part2_validate_file_type_profile(file_type, file_type_box.0.1)"),
            }
            for name, fragments in handoffs.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in fragments):
                    raise ValueError("whole raw file-type Result requires complete actual admission/ordered-brand/prefix models")
        if entry["id"] == _BOX_READER_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_BOX_READER_CONTRACTS):
                raise ValueError("whole raw box reader Result requires actual private/public/shared-init/companion contracts")
            if not _BOX_READER_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _BOX_READER_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw box reader Result requires all actual byte/state/input/payload bridges")
            path = (ROOT / "src/jp2/box_reader.rs").resolve()
            handoffs = {
                "BoxReader::new": ("box_reader_from_input(input, limits)",),
                "BoxType::new": ("box_type_from_bytes(bytes)",),
                "BoxReader::next_box_ref": (
                    "if self.failed", "match self.next_box()", "self.failed = true;",
                ),
                "BoxReader::next_box": (
                    "if self.position == self.input.len()", "self.work_units = self.work_units.checked_add(1)",
                    "let remaining = self.input.len().checked_sub(offset)",
                    "let box_type = box_type_from_bytes(",
                    "if total_length < header_length", "usize::try_from(total_length)",
                    "let end = offset.checked_add(total_length_usize)", "if end > self.input.len()",
                    "if !box_type.equals(BoxType::CONTIGUOUS_CODESTREAM)",
                    "self.metadata_bytes = self.metadata_bytes.checked_add(total_length)",
                    "self.position = end;", "payload: &self.input[payload_start..end]",
                ),
            }
            for name, required in handoffs.items():
                body = _coverage_function_body(source_text(path), function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole raw box reader Result requires actual constructor/byte/counter/limit/payload handoffs")
            for name, argument in (("BoxReader::next_box_ref", "self"), ("BoxReader::next_box", "self"), ("required_box", "reader")):
                text = source_text(path)
                header = function_header(path, name)
                start = text.rfind("#[cfg_attr(verus_keep_ghost, verus_spec(", 0, header.start()) if header else -1
                contract = text[start:header.start()] if start >= 0 else ""
                expected = f"super::box_reader_input_reference(final({argument}))==super::box_reader_input_reference(old({argument}))"
                if expected not in "".join(contract.split()):
                    raise ValueError("whole raw box reader Result requires complete actual input-reference frames")
            model = source_text((ROOT / "specs/jp2_box_reader.rs").resolve())
            required = {
                "part2_box_reader_next_ref": ("if state.failed { (None, state) }", "failed: true, ..next.1"),
                "part2_box_reader_next": ("state.position == state.input.len()", "state.work_units == u64::MAX",
                    "Part2BoxReaderState { work_units: work, ..state }"),
                "part2_box_reader_after_header": (
                    "total_length < header_length", "end > state.input.len()",
                    "kind != crate::jp2::BoxType::CONTIGUOUS_CODESTREAM",
                    "metadata > crate::limits::resource_metadata_byte_limit(&state.limits)",
                    "state.input.subrange(payload_start as int, end as int)",
                    "Part2BoxReaderState { position: end as usize, ..charged }",
                ),
            }
            for name, fragments in required.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in fragments):
                    raise ValueError("whole raw box reader Result requires complete actual state/error/metadata-exemption models")
        if entry["id"] == _JPX_INSPECTION_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPX_INSPECTION_CONTRACTS):
                raise ValueError("whole parsed-file inspection Result requires actual inspection/count contracts")
            if not _JPX_INSPECTION_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _JPX_INSPECTION_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole parsed-file inspection Result requires all actual layer/timeline/duration/error bridges")
            path = (ROOT / "src/jpx/inspection.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "inspect_file"))
            required = (
                "let layer_count = effective_layer_count(file);",
                "let codestream = codestreams.get(index).ok_or_else(invalid_layer)?;",
                "let layer = file.compositing_layer(index)?;",
                "codestream_indices.push(registration.codestream_index);",
                "codestreams.get(usize::from(registration.codestream_index)).ok_or_else(invalid_layer)?",
                "width = width.min(registered_extent(codestream.image_size.width, u32::from(registration.horizontal_subsampling), u32::from(layer.horizontal_grid_size()), registration.horizontal_offset,)?);",
                "height = height.min(registered_extent(codestream.image_size.height, u32::from(registration.vertical_subsampling), u32::from(layer.vertical_grid_size()), registration.vertical_offset,)?);",
                "build_timeline(composition, effective_layer_count(file), limits.maximum_frames(),)",
                "crate::specs::part2_inspection_duration_prefix(frame_views(frames@), frame_index as nat)",
                "instruction_sets: u32::try_from(composition.instruction_sets.len())",
                "metadata_boxes: file.metadata_boxes()", "metadata_depth: file.metadata_depth()",
            )
            normalized = "".join(body.split()) if body is not None else ""
            closure = "".join("""verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_composition_error(true),""".split())
            if body is None or any("".join(item.split()) not in normalized for item in required) \
                    or normalized.count("codestreams.get(index).ok_or_else(invalid_layer)?") != 2 \
                    or normalized.count(closure) != 3 or normalized.count("|_error|arithmetic_overflow()") != 3:
                raise ValueError("whole parsed-file inspection Result requires actual ordered source/registration/timeline/error handoffs")
            model = source_text((ROOT / "specs/jpx_inspection.rs").resolve())
            handoffs = {
                "part2_inspection_layer": (
                    "if index as nat > u16::MAX as nat", "else if index >= geometries.len()",
                    "part2_inspection_registration_prefix(config, geometries, config.registrations.len())",
                ),
                "part2_inspection_registration_step": (
                    "registration.codestream_index as int", "if source >= geometries.len()",
                    "registration.horizontal_subsampling as u32, layer.grid.0 as u32, registration.horizontal_offset",
                    "registration.vertical_subsampling as u32, layer.grid.1 as u32, registration.vertical_offset",
                ),
                "part2_inspection_composition": (
                    "part2_build_timeline(composition.sets,", "part2_inspection_duration_prefix(frames, frames.len())",
                    "composition.sets.len() > u32::MAX as nat", "has_unknown_boxes: composition.has_unknown_boxes",
                ),
            }
            for name, required in handoffs.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole parsed-file inspection Result requires complete actual input/error/output models")
        if entry["id"] == _SOURCE_FRAME_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_SOURCE_FRAME_CONTRACTS):
                raise ValueError("whole source frame Result requires actual frame and owned-image contracts")
            if not _SOURCE_FRAME_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _SOURCE_FRAME_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole source frame Result requires real decoding/rendering and lazy error/metadata bridges")
            path = (ROOT / "src/jpx/render.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "render_inspected_frame"))
            required = (
                "select_frame_instructions(composition.frames(), composition.loop_count(), requested_frame,)",
                "let outcome = decode_effective_layer(file, instruction.layer_index(), options);",
                "let failed = outcome.is_err();",
                "supplied.push((instruction.layer_index, Some(outcome)));",
                "invariant_except_break", "if failed {",
                "crate::specs::part2_frame_source_supplies_step(input, layers, selected, limits, index as nat);",
                "crate::specs::part2_frame_source_supplies_stopped(input, layers, selected, limits, index as nat + 1, selected.len());",
                "render_normalized_frame(composition.width(), composition.height(), composition.frames(), composition.loop_count(), requested_frame, supplied, options.limits().maximum_decoded_bytes(), options.limits(),)",
            )
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                raise ValueError("whole source frame Result requires actual selection/decoding/lazy-break/full-render handoffs")
            path = (ROOT / "src/jpx/layer_decode.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "OwnedLayer::into_image"))
            required = (
                "let pixels = checked_area(self.width, self.height)?;",
                "None => (vec![u16::MAX; pixels], false)",
                "crate::color::from_layer(self.width, self.height, self.color_space, self.colors, alpha, premultiplied,)",
            )
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                raise ValueError("whole source frame Result requires actual owned-image geometry/alpha/output handoffs")
            path = (ROOT / "src/jpx/inspection.rs").resolve()
            text = source_text(path)
            header = function_header(path, "JpxInspection::composition")
            start = text.rfind("#[cfg_attr(verus_keep_ghost, verus_spec(", 0, header.start()) if header else -1
            contract = text[start:header.start()] if start >= 0 else ""
            if "result==inspection_composition_reference(self)" not in "".join(contract.split()):
                raise ValueError("whole source frame Result requires complete actual borrowed-composition preservation")
            model = source_text((ROOT / "specs/jpx_frame.rs").resolve())
            model_handoffs = {
                "part2_frame_source_supplies": (
                    "if previous.1 { previous }", "let index = instructions[count - 1].0;",
                    "part2_decode_effective_layer(file, layers, index, limits)",
                    "previous.0.push((index, Some(outcome)))",
                ),
                "part2_render_inspected_source_frame": (
                    "part2_select_frame(config.3, requested, config.2)",
                    "part2_frame_source_supplies(file, layers, instructions, limits, instructions.len())",
                    "part2_render_normalized_frame(config.0, config.1, config.3, config.2, requested, decoded.0,",
                ),
                "part2_owned_layer_image": (
                    "None => (Seq::new(pixels as nat, |_i: int| u16::MAX), false)",
                ),
            }
            for name, required in model_handoffs.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole source frame Result requires actual ordered source supplies and complete output models")
        if entry["id"] == _EFFECTIVE_LAYER_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_EFFECTIVE_LAYER_CONTRACTS):
                raise ValueError("whole effective layer Result requires both actual complete dispatcher contracts")
            if not _EFFECTIVE_LAYER_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _EFFECTIVE_LAYER_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole effective layer Result requires all actual routing models and metadata/reference bridges")
            path = (ROOT / "src/jpx/layer_decode.rs").resolve()
            handoffs = {
                "decode_effective_layer": (
                    "if file.compositing_layers().is_empty()", "if layer_index >= file.codestream_count()",
                    "owned_layer_from_image(&decode_layer(file, layer_index, None, options)?)",
                    "let layer = file.compositing_layer(layer_index)?;",
                    "decode_compositing_layer(file, layer, layer_index, options)",
                ),
                "decode_compositing_layer": (
                    "!layer.channel_definition_records().is_empty()", "layer.registrations().len() > 1",
                    "matches!(layer.opacity(), Some(LayerOpacity::ChromaKey { .. }))",
                    "decode_general_compositing_layer(file, layer, layer_index, options)",
                    "let color_override = layer.color_group().first();",
                    "let image = decode_layer(file, layer_index, color_override, options)?;",
                    "usize::from(first.codestream_index)", "let alpha_registration = layer.registrations().get(1);",
                    "apply_layer_opacity(file, layer, layer_index, &mut owned, None, options)?;",
                ),
            }
            for name, required in handoffs.items():
                body = _coverage_function_body(source_text(path), function_header(path, name))
                if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                    raise ValueError("whole effective layer Result requires actual routing/source/fallback/registration/opacity handoffs")
            path = (ROOT / "src/jp2/container.rs").resolve()
            text = source_text(path)
            header = function_header(path, "Jp2File::compositing_layer")
            start = text.rfind("#[cfg_attr(verus_keep_ghost, verus_spec(", 0, header.start()) if header else -1
            contract = text[start:header.start()] if start >= 0 else ""
            if "Some(layer)==super::jpx_file_layer_reference(self,index)" not in "".join(contract.split()):
                raise ValueError("whole effective layer Result requires complete actual borrowed-layer reference preservation")
            model = source_text((ROOT / "specs/jpx_dispatch.rs").resolve())
            required = (
                "if index >= file.1.len()", "part2_dispatch_owned_image(file, index, None, limits)",
                "part2_layer_config_lookup(layers, index)",
                "part2_decode_general_layer(file, config, layer_index, limits)",
                "part2_dispatch_owned_image(file, registration.0 as usize, color, limits)",
                "part2_register_layer(owned, registration, geometry.1, geometry.2)",
                "file, config.opacity, geometry, registration.0 as usize, registered,",
            )
            if any("".join(item.split()) not in "".join(model.split()) for item in required):
                raise ValueError("whole effective layer Result requires actual ordered decoder/registration/opacity models")
        if entry["id"] == _GENERAL_LAYER_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_GENERAL_LAYER_CONTRACTS):
                raise ValueError("whole general layer Result requires the actual complete general normalizer contract")
            if not _GENERAL_LAYER_MODELS.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not _GENERAL_LAYER_PROOFS.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole general layer Result requires all actual source/component/definition/output models and error bridges")
            path = (ROOT / "src/jpx/layer_decode.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "decode_general_compositing_layer"))
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in _GENERAL_LAYER_HANDOFFS):
                raise ValueError("whole general layer Result requires actual source/component/definition/output handoffs")
            model = source_text((ROOT / "specs/jpx_general.rs").resolve())
            required_models = {
                "part2_general_source_step": (
                    "part2_decode_jpx_codestream(file, selected.0, limits)",
                    "part2_native_registered_extent(decoded.0.0.0, selected.1 as u32, config.horizontal_grid as u32, selected.3)",
                    "part2_native_registered_extent(decoded.0.0.1, selected.2 as u32, config.vertical_grid as u32, selected.4)",
                ),
                "part2_general_component_step": (
                    "color_normalize_component(component, image.0.0, image.0.1, image.0.2, image.0.3)",
                    "part2_register_component_plane(Part2PlaneRegistration",
                    "source: normalized,", "horizontal_offset: source.3", "vertical_offset: source.4",
                    "image.2[index as int]", "previous.1.push((component.info.precision, component.info.signed))",
                ),
                "part2_general_finish": (
                    "part2_general_definitions(config, colors, components.0)",
                    "part2_typed_image_from_parts(width, height, 0, 0, defined,",
                    "color_convert_jp2(image.1, image.2, image.0, config.color,",
                    "part2_owned_layer_input(converted.0, converted.1, converted.2, converted.4)",
                    "channels as usize != colors || components.1.len() < colors",
                    "part2_normalized_component_chroma_keys(values, components.1.take(colors as int))",
                    "part2_apply_chroma_key(owned, keys)",
                ),
            }
            for name, required in required_models.items():
                actual = _coverage_spec_function_body(model, name)
                if actual is None or any("".join(item.split()) not in "".join(actual.split()) for item in required):
                    raise ValueError("whole general layer Result requires complete actual producer models without supplied banks or trimming")
        if entry["id"] == _COMPONENT_PLANE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_COMPONENT_PLANE_CONTRACTS):
                raise ValueError("whole registration plane Result requires actual component registration contract")
            models = {("specs/jpx_normalization.rs", name) for name in (
                "part2_register_component_plane", "part2_plane_registration_rows", "part2_plane_registration_columns",
            )}
            proofs = {("specs/jpx_normalization.rs", name) for name in (
                "part2_plane_index_bound", "part2_plane_columns_step", "part2_plane_columns_error",
                "part2_plane_rows_step", "part2_plane_rows_error",
            )}
            if not models.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}) \
                    or not proofs.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole registration plane Result requires complete traversal/index/error models and bridges")
            path = (ROOT / "src/jpx/registration.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "register_samples"))
            required = (
                "source: source@, source_width, source_height, width, height,",
                "horizontal_subsampling, vertical_subsampling, horizontal_grid, vertical_grid,",
                "horizontal_offset, vertical_offset,",
                "crate::specs::part2_plane_registration_rows(context, initial, y as nat) == Ok(output@)",
                "crate::specs::part2_plane_registration_columns(context, y, source_y, row_initial, x as nat) == Ok(output@)",
                "crate::specs::part2_plane_rows_step(context, initial, y as nat);",
                "crate::specs::part2_plane_columns_step(context, y, source_y, row_initial, x as nat);",
                "crate::specs::part2_plane_index_bound(width, height, x, y, output.len());",
                "source_y_numerator >= vertical_offset", "source_y < source_height",
                "source_x_numerator >= horizontal_offset", "source_x < source_width",
                "index_of(width, x, y)?", "index_of(source_width, source_x, source_y)?",
            )
            if body is None or any("".join(item.split()) not in "".join(body.split()) for item in required):
                raise ValueError("whole registration plane Result requires actual complete context/row/column/index handoffs")
            source = source_text((ROOT / "specs/jpx_normalization.rs").resolve())
            expected = """
                match part2_layer_area(context.source_width, context.source_height) {
                    Err(error) => Err(error),
                    Ok(source_area) => {
                        if context.source.len() != source_area as nat || context.horizontal_subsampling == 0
                            || context.vertical_subsampling == 0 || context.horizontal_grid == 0 || context.vertical_grid == 0
                        { Err(part2_composition_error(false)) }
                        else {
                            match part2_layer_area(context.width, context.height) {
                                Err(error) => Err(error),
                                Ok(area) => part2_plane_registration_rows(context, Seq::new(area as nat, |_index: int| 0u16), context.height as nat),
                            }
                        }
                    },
                }
            """
            actual = _coverage_spec_function_body(source, "part2_register_component_plane")
            if actual is None or "".join(actual.split()) != "".join(expected.split()):
                raise ValueError("whole registration plane Result requires complete actual admission/zero-seed/traversal model")
        if entry["id"] == _SOURCE_OPACITY_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_SOURCE_OPACITY_CONTRACTS):
                raise ValueError("whole source opacity Result requires actual opacity/source/owner/registration/chroma contracts")
            model_refs = {("specs/jpx_opacity.rs", name) for name in (
                "part2_apply_source_layer_opacity", "part2_source_registered_opacity", "part2_opacity_header_depth",
            )} | {("specs/jpx_source.rs", "part2_decode_jpx_layer")} | {
                ("specs/mod.rs", name) for name in (
                    "part2_owned_layer_input", "part2_register_layer", "part2_copy_registered_opacity",
                    "part2_set_layer_alpha_mode", "part2_normalized_chroma_keys", "part2_apply_chroma_key_policy",
                )
            }
            if not model_refs.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}):
                raise ValueError("whole source opacity Result requires actual source/registration/header-choice models")
            proofs = {
                ("specs/jpx_opacity.rs", "part2_apply_source_layer_opacity_unfold"),
                ("src/jp2/proof_support.rs", "source_opacity_known"),
                ("src/jp2/composition.rs", "CompositingLayer::opacity"),
                ("src/jp2/composition.rs", "CompositingLayer::box_header"),
                ("src/jp2/composition.rs", "CompositingLayer::horizontal_grid_size"),
                ("src/jp2/composition.rs", "CompositingLayer::vertical_grid_size"),
                ("src/jp2/container.rs", "CodestreamBox::codestream_header"),
                ("src/jp2/container.rs", "CodestreamHeaderAssociation::parsed_header"),
            }
            if not proofs.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole source opacity Result requires checked actual getter/opacity/unfold bridges")
            for (relative, symbol), expected in {
                ("src/jp2/composition.rs", "CompositingLayer::opacity"):
                    "super::source_opacity_reference_view(result) == super::source_layer_opacity(self)",
                ("src/jp2/composition.rs", "CompositingLayer::box_header"):
                    "super::box_header_offset(result) == super::source_layer_geometry(self).0",
                ("src/jp2/composition.rs", "CompositingLayer::horizontal_grid_size"):
                    "result == super::source_layer_geometry(self).1",
                ("src/jp2/composition.rs", "CompositingLayer::vertical_grid_size"):
                    "result == super::source_layer_geometry(self).2",
                ("src/jp2/container.rs", "CodestreamBox::codestream_header"):
                    "super::source_optional_association_view(result) == super::codestream_source_view(self).2",
                ("src/jp2/container.rs", "CodestreamHeaderAssociation::parsed_header"):
                    "super::associated_header_option(result) == super::source_association_header_view(self).1",
            }.items():
                path = (ROOT / relative).resolve()
                text = source_text(path)
                header = function_header(path, symbol)
                if header is None:
                    raise ValueError("whole source opacity Result requires actual metadata getter contracts")
                start = text.find("fn", header.start(), header.end())
                attrs = text[text.rfind("#[cfg_attr", 0, start):start]
                wanted = "verus_spec(result=>ensures" + "".join(expected.split()) + ","
                if wanted not in "".join(attrs.split()) or re.search(r"\brequires\b", attrs):
                    raise ValueError("whole source opacity Result requires actual metadata getter contracts")
            path = (ROOT / "src/jpx/opacity.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "apply_layer_opacity"))
            expected = """
                #[cfg(verus_keep_ghost)] proof! {
                    crate::specs::part2_apply_source_layer_opacity_unfold(
                        jp2::jpx_file_decode_view(file), jp2::source_layer_opacity(layer), jp2::source_layer_geometry(layer),
                        color_codestream, owned_layer_view(owned),
                        match alpha_registration { None => None, Some(registration) => Some(layer_registration_view(registration)) },
                        crate::options::decode_options_limits(options));
                }
                let Some(opacity) = layer.opacity() else { return Ok(()); };
                #[cfg(verus_keep_ghost)] proof! { jp2::source_opacity_known(opacity); }
                match opacity {
                    LayerOpacity::Straight | LayerOpacity::Premultiplied => {
                        let premultiplied = matches!(opacity, LayerOpacity::Premultiplied);
                        if let Some(registration) = alpha_registration {
                            let image = decode_layer(file, usize::from(registration.codestream_index), None, options,)?;
                            let alpha_source = owned_layer_from_image(&image)?;
                            let alpha_registered = register_layer(
                                &alpha_source, registration, layer.horizontal_grid_size(), layer.vertical_grid_size(),)?;
                            copy_registered_layer_opacity(owned, &alpha_registered, premultiplied)?;
                        } else {
                            set_layer_alpha_mode(owned, premultiplied, layer.box_header().offset())?;
                        }
                    }
                    LayerOpacity::ChromaKey { channels, values } => {
                        if usize::from(*channels) != owned.colors.len() {
                            return Err(DecodeError::malformed(layer.box_header().offset(), MalformedKind::InvalidBoxContents,));
                        }
                        let header = file.codestream(color_codestream)?.codestream_header()
                            .and_then(
                                #[cfg_attr(verus_keep_ghost, verus_spec(result: (Option<&jp2::Jp2Header>) =>
                                    ensures jp2::associated_header_option(result) == jp2::source_association_header_view(association).1,
                                ))]
                                |association| association.parsed_header(),)
                            .unwrap_or(file.header());
                        #[cfg(verus_keep_ghost)] proof! {
                            assert(crate::specs::part2_opacity_header_depth(jp2::jpx_file_decode_view(file), color_codestream)
                                == Ok(header.image.bit_depth));
                        }
                        let keys = normalized_chroma_keys(values, *channels, header.image.bit_depth)?;
                        apply_chroma_key_with_policy(owned, &keys, true)?;
                    }
                }
                Ok(())
            """
            if body is None or "".join(body.split()) != "".join(expected.split()):
                raise ValueError("whole source opacity Result requires actual source/registration/chroma mutation handoffs")
            projections = {
                ("src/jp2/proof_support.rs", "source_opacity_reference_view"):
                    "match value { None => None, Some(value) => Some(source_opacity_value_view(value)) }",
                ("src/jp2/proof_support.rs", "source_opacity_value_view"): """
                    match value {
                        LayerOpacity::Straight => crate::specs::Part2SourceOpacity::Straight,
                        LayerOpacity::Premultiplied => crate::specs::Part2SourceOpacity::Premultiplied,
                        LayerOpacity::ChromaKey { channels, values } =>
                            crate::specs::Part2SourceOpacity::ChromaKey { channels: *channels, values: values@ },
                    }
                """,
                ("src/jp2/proof_support.rs", "source_layer_opacity"):
                    "match &layer.opacity { None => None, Some(opacity) => Some(source_opacity_value_view(opacity)) }",
                ("src/jp2/proof_support.rs", "source_layer_geometry"):
                    "(layer.header.offset, layer.horizontal_grid_size, layer.vertical_grid_size)",
                ("src/jp2/proof_support.rs", "source_association_header_view"): """
                    (association.header.offset, match &association.parsed {
                        None => None, Some(header) => Some(associated_header_view(header)),
                    })
                """,
                ("src/jp2/proof_support.rs", "source_optional_association_view"):
                    "match association { None => None, Some(association) => Some(source_association_header_view(association)) }",
                ("specs/jpx_opacity.rs", "part2_opacity_header_depth"): """
                    match part2_jpx_codestream_lookup(file.1, index) {
                        Err(error) => Err(error),
                        Ok(source) => {
                            let header = match source.2 {
                                None => file.2,
                                Some(association) => match association.1 { None => file.2, Some(header) => header },
                            };
                            Ok(header.1.bit_depth)
                        },
                    }
                """,
                ("specs/jpx_opacity.rs", "part2_source_registered_opacity"): """
                    match part2_decode_jpx_layer(file, registration.0 as usize, None, limits) {
                        Err(error) => (Err(error), owned),
                        Ok(image) => match part2_owned_layer_input(image.0, image.1, image.2, image.4) {
                            Err(error) => (Err(error), owned),
                            Ok(source) => match part2_register_layer(source, registration, grid.0, grid.1) {
                                Err(error) => (Err(error), owned),
                                Ok(registered) => part2_copy_registered_opacity(owned, registered, premultiplied),
                            },
                        },
                    }
                """,
                ("specs/jpx_opacity.rs", "part2_apply_source_layer_opacity"): """
                    match opacity {
                        None => (Ok(()), owned),
                        Some(Part2SourceOpacity::Straight) | Some(Part2SourceOpacity::Premultiplied) => {
                            let premultiplied = opacity == Some(Part2SourceOpacity::Premultiplied);
                            match registration {
                                None => part2_set_layer_alpha_mode(owned, premultiplied, geometry.0),
                                Some(registration) => part2_source_registered_opacity(
                                    file, registration, (geometry.1, geometry.2), owned, premultiplied, limits),
                            }
                        },
                        Some(Part2SourceOpacity::ChromaKey { channels, values }) => {
                            if channels as usize != owned.3.len() {
                                (Err(crate::DecodeError::MalformedInput {
                                    offset: geometry.0, kind: crate::MalformedKind::InvalidBoxContents,
                                }), owned)
                            } else {
                                match part2_opacity_header_depth(file, color_codestream) {
                                    Err(error) => (Err(error), owned),
                                    Ok(depth) => match part2_normalized_chroma_keys(values, channels, depth) {
                                        Err(error) => (Err(error), owned),
                                        Ok(keys) => part2_apply_chroma_key_policy(owned, keys, true),
                                    },
                                }
                            }
                        },
                    }
                """,
            }
            for (relative, symbol), expected in projections.items():
                actual = _coverage_spec_function_body(source_text((ROOT / relative).resolve()), symbol)
                if actual is None or "".join(actual.split()) != "".join(expected.split()):
                    raise ValueError("whole source opacity Result requires complete source/metadata/owner projections, not image banks")
        if entry["id"] == _JPX_LAYER_COLOR_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPX_LAYER_COLOR_CONTRACTS):
                raise ValueError("whole JPX layer color Result requires actual layer/source/complete conversion contracts")
            model_refs = {
                ("specs/jpx_source.rs", "part2_decode_jpx_layer"),
                ("specs/jpx_source.rs", "part2_decode_jpx_codestream"),
                ("specs/mod.rs", "color_convert_jp2"),
            }
            if not model_refs.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}):
                raise ValueError("whole JPX layer color Result requires actual source-to-conversion models")
            proof_refs = {
                ("specs/jpx_source.rs", "part2_decode_jpx_layer_unfold"),
                ("src/decode/proof_support.rs", "associated_typed_errors_known"),
                ("src/decode/proof_support.rs", "associated_typed_success_known"),
                ("src/jp2/proof_support.rs", "optional_color_specification_method"),
                ("src/jp2/container.rs", "Jp2File::header"),
                ("src/options.rs", "DecodeOptions::limits"),
            }
            if not proof_refs.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole JPX layer color Result requires actual outcome/override/header/limits bridges")
            path = (ROOT / "src/jpx/layer_decode.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "decode_layer"))
            expected = """
                #[cfg(verus_keep_ghost)] proof! {
                    crate::decode::associated_typed_errors_known();
                    crate::specs::part2_decode_jpx_layer_unfold(
                        jp2::jpx_file_decode_view(file), codestream_index,
                        jp2::optional_color_specification_method(color_override), crate::options::decode_options_limits(options));
                }
                let (decoded, header) = crate::decode::decode_jpx_file(file, codestream_index, options)?;
                #[cfg(verus_keep_ghost)] proof! { crate::decode::associated_typed_success_known(&decoded, header); }
                let header = header.unwrap_or(file.header());
                crate::color::convert_jp2_color(
                    &decoded, color_override.unwrap_or(&header.color), options.limits(),)
            """
            if body is None or "".join(body.split()) != "".join(expected.split()):
                raise ValueError("whole JPX layer color Result requires real source/header/override/conversion handoffs")
            for (relative, symbol), expected in {
                ("src/jp2/proof_support.rs", "optional_color_specification_method"):
                    "match color { None => None, Some(color) => Some(color_specification_method(color)) }",
                ("specs/jpx_source.rs", "part2_decode_jpx_layer"): """
                    match part2_decode_jpx_codestream(input, index, limits) {
                        Err(error) => Err(error),
                        Ok(decoded) => {
                            let color = match color_override {
                                Some(color) => color,
                                None => match decoded.1 { Some(header) => header.2, None => input.2.2 },
                            };
                            color_convert_jp2(decoded.0.1, decoded.0.2, decoded.0.0, color,
                                crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits))
                        },
                    }
                """,
            }.items():
                actual = _coverage_spec_function_body(source_text((ROOT / relative).resolve()), symbol)
                if actual is None or "".join(actual.split()) != "".join(expected.split()):
                    raise ValueError("whole JPX layer color Result requires actual complete source/override models, not decoded-image banks")
        if entry["id"] == _JPX_SOURCE_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_JPX_SOURCE_CONTRACTS):
                raise ValueError("whole JPX source Result requires actual file, raw info/decoder, association/validation/output contracts")
            model_refs = {
                ("specs/jpx_source.rs", name) for name in (
                    "part2_decode_jpx_codestream", "part2_decode_jpx_source", "part2_decode_jpx_associated",
                    "part2_file_type_compatible", "part2_file_type_jpx", "part2_jpx_codestream_lookup",
                )
            } | {
                ("specs/raw_layout.rs", "part1_parse_info"), ("specs/raw_decode.rs", "part2_decode_raw_codestream"),
                ("specs/mod.rs", "part2_associated_codestream_header"),
                ("specs/mod.rs", "part2_validate_selected_header"), ("specs/mod.rs", "part2_apply_associated_output"),
            }
            if not model_refs.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}):
                raise ValueError("whole JPX source Result requires the complete actual source/header/raw decoder/output model chain")
            required_proofs = {
                ("specs/jpx_source.rs", name) for name in (
                    "part2_decode_jpx_codestream_unfold", "part2_decode_jpx_source_unfold", "part2_decode_jpx_associated_unfold",
                )
            } | {
                ("src/codestream/proof_support.rs", "complete_codestream_info_errors_known"),
                ("src/codestream/proof_support.rs", "complete_codestream_info_known_fields"),
                ("src/jp2/proof_support.rs", "codestream_source_known_fields"),
                ("src/jp2/proof_support.rs", "jpx_file_associated_header_reference_unfold"),
                ("src/jp2/proof_support.rs", "jpx_file_associated_header_reference"),
                ("src/jp2/proof_support.rs", "jpx_file_codestream_reference"),
                ("src/jp2/proof_support.rs", "jpx_file_header_reference"),
                ("src/jp2/proof_support.rs", "associated_header_reference"),
            }
            getters = {
                ("src/jp2/box_reader.rs", "BoxType::equals"): "result == (self == other)",
                ("src/jp2/box_reader.rs", "BoxHeader::offset"): "result == super::box_header_offset(self)",
                ("src/jp2/container.rs", "FileType::is_compatible_with"):
                    "result == crate::specs::part2_file_type_compatible(super::file_type_view(self), brand)",
                ("src/jp2/container.rs", "FileType::is_jpx_compatible"):
                    "result == crate::specs::part2_file_type_jpx(super::file_type_view(self))",
                ("src/jp2/container.rs", "CodestreamBox::box_header"):
                    "super::box_header_offset(result) == super::codestream_source_view(self).1",
                ("src/jp2/container.rs", "CodestreamBox::data"): "result@ == super::codestream_source_view(self).0",
                ("src/jp2/container.rs", "Jp2File::file_type"):
                    "super::file_type_view(result) == super::jpx_file_decode_view(self).0",
                ("src/jp2/container.rs", "Jp2File::header"):
                    "super::associated_header_view(result) == super::jpx_file_decode_view(self).2,"
                    "result == super::jpx_file_header_reference(self)",
                ("src/jp2/container.rs", "Jp2File::codestream"): """
                    match result {
                        Err(error) => crate::specs::part2_jpx_codestream_lookup(
                            super::jpx_file_decode_view(self).1, index) == Err(error),
                        Ok(stream) => crate::specs::part2_jpx_codestream_lookup(
                            super::jpx_file_decode_view(self).1, index) == Ok(super::codestream_source_view(stream)),
                    },
                    match result {
                        Err(_) => true,
                        Ok(stream) => Some(stream) == super::jpx_file_codestream_reference(self, index),
                    }
                """,
                ("src/options.rs", "DecodeOptions::limits"): "result == decode_options_limits(self)",
            }
            if not (required_proofs | set(getters)).issubset(
                {(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}
            ):
                raise ValueError("whole JPX source Result requires every checked source/getter/error/unfolding bridge")
            for (relative, symbol), expected in getters.items():
                path = (ROOT / relative).resolve()
                text = source_text(path)
                header = function_header(path, symbol)
                if header is None:
                    raise ValueError("whole JPX source Result requires actual getter/reference contracts")
                start = text.find("fn", header.start(), header.end())
                attrs = text[text.rfind("#[cfg_attr", 0, start):start]
                wanted = "verus_spec(result=>ensures" + "".join(expected.split()) + ","
                if wanted not in "".join(attrs.split()) or re.search(r"\brequires\b", attrs):
                    raise ValueError("whole JPX source Result requires actual getter/reference contracts")
            for (relative, symbol), expected in {
                ("src/decode/output.rs", "decode_jpx_file"): """
                    match result {
                        Err(_) => true,
                        Ok(output) => output.1 == jp2::jpx_file_associated_header_reference(file, codestream_index),
                    }
                """,
                ("src/decode/output.rs", "apply_associated_output"):
                    "match result { Err(_) => true, Ok(output) => output.1 == header }",
                ("src/jp2/container.rs", "associated_header_for_codestream"):
                    "result == super::associated_header_reference(selected, fallback)",
            }.items():
                path = (ROOT / relative).resolve()
                text = source_text(path)
                header = function_header(path, symbol)
                if header is None:
                    raise ValueError("whole JPX source Result lacks executable Verus contract: full returned-header frames")
                start = text.find("fn", header.start(), header.end())
                attrs = text[text.rfind("#[cfg_attr", 0, start):start]
                if "".join(expected.split()) + "," not in "".join(attrs.split()) or re.search(r"\brequires\b", attrs):
                    raise ValueError("whole JPX source Result lacks executable Verus contract: full returned-header frames")
            path = (ROOT / "src/decode/output.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "decode_jpx_file"))
            nested = _coverage_function_header(body, "decode_jpx_file_selected") if body is not None else None
            disabled = re.search(r"#\[\s*cfg\s*\(\s*any\s*\(\s*\)\s*\)\s*\]\s*", body) if body is not None else None
            if body is None or nested is None or disabled is None or body[disabled.end():nested.start()].strip():
                raise ValueError("whole JPX source Result requires the preserved nonexecuting nested item")
            opening = body.find("{", nested.end())
            closing = re.search(rf"(?m)^{re.escape(nested[1])}\}}", body[opening + 1:])
            if closing is None or "verus_keep_ghost" in body[disabled.start():opening + 1 + closing.end()]:
                raise ValueError("whole JPX source Result cannot use a disabled nested proof as the real handoff")
            body = body[:disabled.start()] + body[opening + 1 + closing.end():]
            expected = """
                #[cfg(verus_keep_ghost)] proof! {
                    reveal(associated_typed_outcome);
                    codestream::complete_codestream_info_errors_known();
                    jp2::jpx_file_associated_header_reference_unfold(file, codestream_index);
                    crate::specs::part2_decode_jpx_codestream_unfold(
                        jp2::jpx_file_decode_view(file), codestream_index, crate::options::decode_options_limits(options));
                }
                if !file.file_type().is_jpx_compatible() {
                    return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
                }
                let selected = file.codestream(codestream_index)?;
                #[cfg(verus_keep_ghost)] proof! {
                    jp2::codestream_source_known_fields(selected);
                    crate::specs::part2_decode_jpx_source_unfold(
                        jp2::codestream_source_view(selected), jp2::jpx_file_decode_view(file).2,
                        crate::options::decode_options_limits(options));
                }
                let associated_header = Some(jp2::associated_header_for_codestream(selected, file.header(),)?);
                #[cfg(verus_keep_ghost)] proof! {
                    crate::specs::part2_decode_jpx_associated_unfold(
                        jp2::codestream_source_view(selected), jp2::associated_header_view(associated_header.unwrap()),
                        crate::options::decode_options_limits(options));
                }
                let info = codestream::parse(selected.data(), options.limits())?;
                #[cfg(verus_keep_ghost)] proof! { codestream::complete_codestream_info_known_fields(&info); }
                if let Some(header) = associated_header {
                    jp2::validate_selected_header(header, &info, selected.box_header().offset())?;
                }
                let decoded = decode_codestream(selected.data(), options)?;
                apply_associated_output(decoded, associated_header, options.limits())
            """
            if "".join(body.split()) != "".join(expected.split()):
                raise ValueError("whole JPX source Result requires actual executing source/header/raw decoder/output handoffs")
            projections = {
                ("src/jp2/proof_support.rs", "file_type_view"):
                    "(file_type.brand, file_type.minor_version, file_type.compatible_brands@)",
                ("src/jp2/proof_support.rs", "codestream_source_view"):
                    "(stream.data@, stream.header.offset, codestream_header_association_view(stream))",
                ("src/jp2/proof_support.rs", "jpx_file_decode_view"): """
                    (file_type_view(&file.file_type),
                        file.codestreams@.map_values(|stream: CodestreamBox| codestream_source_view(&stream)),
                        associated_header_view(&file.header))
                """,
                ("src/jp2/proof_support.rs", "jpx_file_codestream_reference"): """
                    if index < file.codestreams@.len() {
                        Some(&file.codestreams@[index as int])
                    } else {
                        None
                    }
                """,
                ("src/jp2/proof_support.rs", "jpx_file_header_reference"): "&file.header",
                ("src/jp2/proof_support.rs", "associated_header_reference"): """
                    match &selected.codestream_header {
                        None => Ok(fallback),
                        Some(association) => match &association.parsed {
                            Some(header) => Ok(header),
                            None => Err(DecodeError::MalformedInput {
                                offset: association.header.offset, kind: MalformedKind::MissingRequiredStructure,
                            }),
                        },
                    }
                """,
                ("src/jp2/proof_support.rs", "jpx_file_associated_header_reference"): """
                    match jpx_file_codestream_reference(file, index) {
                        None => None,
                        Some(selected) => match associated_header_reference(selected, jpx_file_header_reference(file)) {
                            Err(_) => None,
                            Ok(header) => Some(header),
                        },
                    }
                """,
                ("specs/jpx_source.rs", "part2_file_type_compatible"): "input.0 == brand || input.2.contains(brand)",
                ("specs/jpx_source.rs", "part2_file_type_jpx"): """
                    part2_file_type_compatible(input, crate::jp2::BoxType::JPX_BRAND)
                        || part2_file_type_compatible(input, crate::jp2::BoxType::JPX_BASELINE_BRAND)
                """,
                ("specs/jpx_source.rs", "part2_jpx_codestream_lookup"): """
                    if index < input.len() { Ok(input[index as int]) }
                    else { Err(crate::DecodeError::CodestreamIndexOutOfRange { index, codestreams: input.len() as usize }) }
                """,
                ("specs/jpx_source.rs", "part2_decode_jpx_codestream"): """
                    if !part2_file_type_jpx(input.0) {
                        Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidProfile })
                    } else {
                        match part2_jpx_codestream_lookup(input.1, index) {
                            Err(error) => Err(error),
                            Ok(source) => part2_decode_jpx_source(source, input.2, limits),
                        }
                    }
                """,
                ("specs/jpx_source.rs", "part2_decode_jpx_source"): """
                    match part2_associated_codestream_header(source.2, fallback) {
                        Err(error) => Err(error),
                        Ok(header) => part2_decode_jpx_associated(source, header, limits),
                    }
                """,
                ("specs/jpx_source.rs", "part2_decode_jpx_associated"): """
                    match part1_parse_info(source.0, limits) {
                        Err(error) => Err(error),
                        Ok(info) => match part2_validate_selected_header(
                            header.1, info.0.image_size.geometry.0, info.0.image_size.geometry.1,
                            info.0.image_size.components, info.0.image_size.uniform_bit_depth,
                            info.0.image_size.uniform_signed, source.1,
                        ) {
                            Err(error) => Err(error),
                            Ok(()) => match part2_decode_raw_codestream(source.0, limits, None) {
                                Err(error) => Err(error),
                                Ok(image) => part2_apply_associated_output(image, Some(header),
                                    crate::limits::resource_component_limit(limits),
                                    crate::limits::resource_decoded_bytes_limit(limits)),
                            },
                        },
                    }
                """,
            }
            for (relative, symbol), expected in projections.items():
                path = (ROOT / relative).resolve()
                actual = _coverage_spec_function_body(source_text(path), symbol)
                if actual is None or "".join(actual.split()) != "".join(expected.split()):
                    raise ValueError("whole JPX source Result requires complete physical/source models, not supplied banks or trimming")
        if entry["id"] == _RAW_RECONSTRUCTED_ENTRY:
            if {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]} != set(_RAW_RECONSTRUCTED_CONTRACTS):
                raise ValueError("strict raw reconstruction Result requires the public API and both output admissions")
        if entry["id"] == _RAW_TYPED_ENTRY:
            actual = {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]}
            if actual != set(_RAW_TYPED_CONTRACTS):
                raise ValueError("whole raw typed Result requires both raw APIs, actual raw parser and complete decoder/type producers")
            model_refs = {
                ("specs/raw_decode.rs", "part2_decode_raw_codestream"),
                ("specs/decoder_input.rs", "part2_decoder_input_from_raw"),
                ("specs/decoder_input.rs", "part2_decoder_tile_from_raw"),
                ("specs/decoder_input.rs", "part2_decode_typed_layout_input"),
                ("specs/decoder_input.rs", "part2_decode_layout_input"),
                ("specs/decoder_input.rs", "part2_decode_layout_selected_input"),
                ("specs/decoder_input.rs", "part2_typed_layout_input"),
                ("specs/decoder_input.rs", "part2_collect_nonlinear_regions_input"),
            }
            if not model_refs.issubset({(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}):
                raise ValueError("whole raw typed Result model must bind the actual complete source/decoder/nonlinear chain")
            path = (ROOT / "src/decode/api.rs").resolve()
            text = source_text(path)
            for name, requested in (("decode_codestream", "None"),
                                    ("decode_codestream_selected", _coverage_call("Some", "selection"))):
                body = _coverage_function_body(text, function_header(path, name))
                prefix = (
                    r"\s*#\[\s*cfg\s*\(\s*verus_keep_ghost\s*\)\s*\]\s*proof!\s*\{\s*"
                    + _coverage_call("codestream::decoder_layout_errors_known") + r"\s*;\s*"
                    + _coverage_call("crate::specs::part2_decode_raw_codestream_unfold",
                                     "input@", _coverage_call("crate::options::decode_options_limits", "options"), requested)
                    + r"\s*;\s*" + _coverage_call("reveal", "crate::specs::part2_decode_typed_layout") + r"\s*;\s*\}\s*"
                )
                parsed = r"let\s+layout\s*=\s*" + _coverage_call(
                    "codestream::parse_layout", "input", _coverage_call("options.limits"),
                ) + r"\s*\?\s*;\s*"
                bridge = (
                    r"#\[\s*cfg\s*\(\s*verus_keep_ghost\s*\)\s*\]\s*proof!\s*\{\s*"
                    + _coverage_call("codestream::decoder_layout_input_matches_raw", r"&\s*layout") + r"\s*;\s*\}\s*"
                )
                decoded = _coverage_call("decode_typed_layout", _coverage_call("input.len"), r"&\s*layout",
                                         _coverage_call("options.limits"), requested) + r"\s*"
                if body is None or re.fullmatch(prefix + parsed + bridge + decoded, body) is None:
                    raise ValueError("whole raw typed Result not used by claimed implementation: actual raw parser/projection/decoder handoff")
            options_path = (ROOT / "src/options.rs").resolve()
            options_text = source_text(options_path)
            getter = function_header(options_path, "DecodeOptions::limits")
            if getter is None:
                raise ValueError("whole raw typed Result requires actual options-limit reference contract")
            start = options_text.find("fn", getter.start(), getter.end())
            attrs = options_text[options_text.rfind("#[cfg_attr", 0, start):start]
            if re.search(
                r"verus_spec\s*\(\s*(\w+)\s*=>\s*ensures\s+\1\s*==\s*"
                + _coverage_call("decode_options_limits", "self"), attrs,
            ) is None:
                raise ValueError("whole raw typed Result requires actual options-limit reference contract")
            projections = {
                ("src/codestream/decoder_input_proof_support.rs", "decoder_layout_input_view"): """
                    crate::specs::Part2DecoderLayoutInput {
                        size: layout.info.image_size,
                        main_execution: (
                            layout.info.component_coding_styles,
                            part2_execution_registry(&layout.info.part2_extensions),
                            part2_kernel_registry(&layout.info.part2_extensions),
                            part2_component_depths(&layout.info.part2_extensions),
                        ),
                        main_extensions: owned_extensions_view(&layout.info.part2_extensions),
                        parts: tile_parts_owned_view(layout.tile_parts@),
                        capabilities: codestream_profile_capabilities(&layout.info.profile),
                    }
                """,
                ("specs/decoder_input.rs", "part2_decoder_input_from_raw"): """
                    Part2DecoderLayoutInput {
                        size: crate::codestream::decoder_native_size(raw.0.image_size),
                        main_execution: part2_decoder_execution_header(
                            crate::codestream::tile_part_native_styles(raw.0.styles), raw.0.extensions),
                        main_extensions: raw.0.extensions,
                        parts: raw.4.map_values(|value: Part1TilePartPayload| part2_decoder_tile_from_raw(value)),
                        capabilities: raw.1.2,
                    }
                """,
                ("specs/raw_decode.rs", "part2_decode_raw_codestream"): """
                    match part1_parse_layout(input, limits) {
                        Err(error) => Err(error),
                        Ok(layout) => part2_decode_typed_layout_input(
                            input.len() as usize, part2_decoder_input_from_raw(layout), limits, requested),
                    }
                """,
            }
            for (name, symbol), expected in projections.items():
                source = source_text((ROOT / name).resolve())
                projected = _coverage_spec_function_body(source, symbol)
                if projected is None or re.sub(r"\s+", "", projected) != re.sub(r"\s+", "", expected):
                    raise ValueError(f"whole raw typed Result requires complete raw/physical projection, not a layout/image bank: {symbol}")
            required_proofs = {
                ("src/codestream/decoder_input_proof_support.rs", name) for name in (
                    "decoder_native_size_inverse", "decoder_native_style_inverse", "decoder_native_quantization_inverse",
                    "decoder_native_roi_inverse", "decoder_native_component_styles_inverse",
                    "decoder_execution_header_fields", "decoder_tile_input_matches_raw", "decoder_layout_input_matches_raw",
                    "decoder_layout_errors_known",
                )
            } | {
                ("specs/raw_decode.rs", "part2_decode_raw_codestream_unfold"),
                ("src/decode/proof_support.rs", "decoder_execution_inputs_known"),
                ("src/options.rs", "DecodeOptions::limits"),
            }
            if not required_proofs.issubset({(ref["path"], ref["symbol"]) for ref in entry["proof_refs"]}):
                raise ValueError("whole raw typed Result requires checked complete Copy inverses/projection/error/unfolding bridges")
        if entry["id"] == _RAW_LAYOUT_ENTRY:
            expected = set(_RAW_LAYOUT_CONTRACTS)
            actual = {(ref["path"], ref["symbol"]) for ref in entry["contract_refs"]}
            if actual != expected:
                raise ValueError("whole raw layout requires internal and both public complete Result contracts")
            model_names = {
                "part1_parse_layout", "part1_parse_info", "part1_read_layout",
                "part1_layout_from_main_result", "part1_layout_continuation", "part1_layout_tile_part",
                "part1_layout_inherited_tile_part", "part1_layout_after_tiles", "part1_layout_profile_tiles",
            }
            if not {("specs/raw_layout.rs", name) for name in model_names}.issubset(
                {(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}
            ):
                raise ValueError("whole raw layout model must bind the raw source-derived chain")
            path = (ROOT / "src/codestream/layout.rs").resolve()
            body = _coverage_function_body(source_text(path), function_header(path, "Parser::parse_layout"))
            public_body = _coverage_function_body(source_text(path), function_header(path, "parse_layout"))
            if public_body is None or re.fullmatch(_RAW_LAYOUT_WRAPPER_BODY, public_body) is None:
                raise ValueError("whole raw layout requires the actual byte/limits reader wrapper")
            state = _coverage_call("persistent_tile_state_view", *(name + r"\s*@" for name in _PERSISTENT_TILE_STATE_FIELDS))
            reader = _coverage_call("parser_view", r"&\s*parser")
            if body is None or any(re.search(pattern, body) is None for pattern in (
                r"let\s+ghost\s+initial_reader\s*=\s*" + _coverage_call("parser_view", r"&\s*self"),
                r"let\s+ghost\s+layout_goal\s*=\s*" + _coverage_call("crate::specs::part1_read_layout", "initial_reader"),
                r"input_length\s*==\s*" + _coverage_call("crate::specs::part1_parse_layout_prologue", "initial_reader")
                + r"\.1\.input\.len\s*\(\s*\)\s+as\s+usize",
                r"invariant_except_break\s+layout_goal\s*==\s*"
                + _coverage_call("crate::specs::part1_layout_continuation", reader, "complete_main", "tile_parts", state, "input_length"),
                r"ensures\s+layout_goal\s*==\s*"
                + _coverage_call("crate::specs::part1_layout_after_tiles", reader, "complete_main", "tile_parts", state),
            )):
                raise ValueError("whole raw layout requires actual reader/counter/eight-state/payload continuation and terminal Result")
            limit_path = (ROOT / "src/error.rs").resolve()
            limit_text = source_text(limit_path)
            limit_header = function_header(limit_path, "DecodeError::limit")
            if limit_header is None:
                raise ValueError("whole raw layout requires the actual complete limit-error constructor contract")
            limit_position = limit_text.find("fn", limit_header.start())
            limit_start = limit_text.rfind("#[cfg_attr", 0, limit_position)
            if re.search(
                r"verus_spec\s*\(\s*ensures\s+returns\s*\(\s*Self::LimitExceeded\s*\{\s*"
                r"resource\s*,\s*limit\s*,\s*actual\s*,?\s*\}\s*\)\s*,?\s*\)",
                limit_text[limit_start:limit_position],
            ) is None:
                raise ValueError("whole raw layout requires the actual complete limit-error constructor contract")
            projections = {
                "complete_codestream_info_view": """
                    (
                        main_header_fields_view(&value.image_size, value.coding_style, &value.quantization,
                            &value.component_coding_styles, &value.component_quantizations, &value.roi_shifts,
                            &value.progression_changes, &value.multiple_component_transform, &value.part2_extensions,
                            value.profile.r_siz, &value.profile.extended_capabilities, &value.profile.profile,
                            &value.profile.corresponding_profile, value.main_header_segments),
                        complete_codestream_profile_view(&value.profile), value.tile_parts, value.consumed_bytes,
                    )
                """,
                "complete_codestream_info_outcome": """
                    match value { Err(error) => Err(error), Ok(info) => Ok(complete_codestream_info_view(&info)) }
                """,
                "complete_layout_outcome": """
                    match value {
                        Err(error) => Err(error),
                        Ok(layout) => {
                            let info = complete_codestream_info_view(&layout.info);
                            Ok((info.0, info.1, info.2, info.3,
                                layout.tile_parts@.map_values(|part: TilePartPayload<'_>| tile_part_payload_view(&part))))
                        },
                    }
                """,
                "optional_capabilities_view": """
                    match value { None => None, Some(caps) => Some(extended_capabilities_view(caps)) }
                """,
                "optional_profile_number_view": """
                    match value { None => None, Some(number) => Some(profile_number_view(number)) }
                """,
                "complete_codestream_profile_view": """
                    (value.r_siz, value.block_coding, optional_capabilities_view(&value.extended_capabilities),
                     optional_profile_number_view(&value.profile), optional_profile_number_view(&value.corresponding_profile))
                """,
            }
            projection_source = source_text((ROOT / "src/codestream/proof_support.rs").resolve())
            for name, expected_body in projections.items():
                projection_headers = list(re.finditer(
                    r"(?m)^([ \t]*)pub(?:\(crate\))?[ \t]+closed[ \t]+spec[ \t]+fn[ \t]+" + re.escape(name) + r"\b",
                    projection_source,
                ))
                projected = (_coverage_function_body(projection_source, projection_headers[0])
                             if len(projection_headers) == 1 else None)
                if projected is None or re.sub(r"\s+", "", projected) != re.sub(r"\s+", "", expected_body):
                    raise ValueError(f"whole raw layout requires complete physical returned projection: {name}")
            model_source = source_text((ROOT / "specs/raw_layout.rs").resolve())
            raw_models = {
                "part1_read_layout": """
                    part1_layout_from_main_result(part1_read_main_header(reader),
                        part1_parse_layout_prologue(reader).1.input.len() as usize)
                """,
                "part1_parse_layout": """
                    match part1_codestream_reader_new(input, limits) {
                        Err(error) => Err(error), Ok(reader) => part1_read_layout(reader),
                    }
                """,
                "part1_parse_info": """
                    match part1_parse_layout(input, limits) {
                        Err(error) => Err(error), Ok(layout) => Ok((layout.0, layout.1, layout.2, layout.3)),
                    }
                """,
            }
            for name, expected_body in raw_models.items():
                model_headers = list(re.finditer(
                    r"(?m)^([ \t]*)pub(?:\(crate\))?[ \t]+(?:open|closed)[ \t]+spec[ \t]+fn[ \t]+"
                    + re.escape(name) + r"\b", model_source,
                ))
                modeled = (_coverage_function_body(model_source, model_headers[0])
                           if len(model_headers) == 1 else None)
                if modeled is None or re.sub(r"\s+", "", modeled) != re.sub(r"\s+", "", expected_body):
                    raise ValueError(f"whole raw layout requires raw byte/reader model, not a result bank: {name}")
            for reference, pattern in (
                ({"path": "src/decode/api.rs", "symbol": "decode_codestream"},
                 _coverage_call("codestream::parse_layout", "input", _coverage_call("options.limits"))),
                ({"path": "src/decode/output.rs", "symbol": "decode_jpx_file"},
                 _coverage_call("codestream::parse", _coverage_call("selected.data"), _coverage_call("options.limits"))),
            ):
                caller_path = (ROOT / reference["path"]).resolve()
                caller_body = (_coverage_function_body(source_text(caller_path), function_header(caller_path, reference["symbol"]))
                               if reference in entry["implementation_refs"] else None)
                if caller_body is None or re.search(pattern, caller_body) is None:
                    raise ValueError("whole raw layout not used by claimed implementation: actual raw consumers required")
        if entry["id"] in (
            "part1-complete-native-codestream-profile-result", "part1-complete-native-raw-main-header-result",
        ):
            main_header = entry["id"] == "part1-complete-native-raw-main-header-result"
            expected = ({_MAIN_HEADER_LAYOUT, *_MAIN_HEADER_INITIALIZER_CONTRACTS}
                        if main_header else set(_PROFILE_RESULT_CONTRACTS))
            actual = {(item["path"], item["symbol"]) for item in entry["contract_refs"]}
            if actual != expected:
                if main_header:
                    raise ValueError("whole raw main-header Result requires actual layout and all three initializer contracts")
                raise ValueError("whole profile Result requires classifier, validation, flag fold and every consumed capability contract")
            if {"path": "src/codestream/layout.rs", "symbol": "Parser::parse_layout"} not in entry["implementation_refs"]:
                raise ValueError("whole profile Result not used by claimed implementation: actual layout required")
            if not main_header and {"path": "specs/codestream_profile.rs", "symbol": "part1_classify_codestream_profile"} not in entry["spec_refs"]:
                raise ValueError("whole profile Result model must be bound to specs/codestream_profile.rs")
            path = (ROOT / "src/codestream/proof_support.rs").resolve()
            projections = {
                "optional_capabilities_view": "match value { None => None, Some(caps) => Some(extended_capabilities_view(caps)) }",
                "optional_profile_number_view": "match value { None => None, Some(number) => Some(profile_number_view(number)) }",
                "complete_codestream_profile_view": """
                    (value.r_siz, value.block_coding, optional_capabilities_view(&value.extended_capabilities),
                     optional_profile_number_view(&value.profile), optional_profile_number_view(&value.corresponding_profile))
                """,
                "complete_codestream_profile_outcome": """
                    match value { Err(error) => Err(error), Ok(profile) => Ok(complete_codestream_profile_view(&profile)) }
                """,
                "profile_tile_inputs_view": """
                    values.map_values(|value: TilePartPayload<'_>| crate::specs::Part1ProfileTile {
                        styles: component_style_owner_view(&value.component_coding_styles),
                        roi: roi_shifts_view(&value.roi_shifts), has_roi: value.has_roi_marker,
                        has_functional: value.has_functional_header_marker,
                    })
                """,
            }
            if main_header:
                projections.update({
                    "main_header_accumulator_view": """
                        crate::specs::Part1MainHeaderAccumulator {
                            image_size: parsed_image_size_view(size), r_siz, start, segments,
                            coding_style: match style { None => None, Some(style) => Some(parsed_coding_style_view(style)) },
                            qcd: optional_segment_view(qcd), coc: segment_slots_view(coc), qcc: segment_slots_view(qcc),
                            roi: roi_shifts_view(roi), roi_seen,
                            plm: packet_length_groups_view(plm), next_plm, plm_seen, ppm, next_ppm, ppm_fragments,
                            progression: progression_changes_view(progression), poc_seen,
                            arrays: mct_arrays_view(arrays), records: mct_records_view(records),
                            order: match order { None => None, Some(order) => Some(order@) },
                            pending_mct: mct_pending_view(pending_mct), completed_mct,
                            pending_mcc: mcc_pending_view(pending_mcc), completed_mcc,
                            capabilities: optional_capabilities_view(capabilities),
                            profile: optional_profile_number_view(profile),
                            corresponding_profile: optional_profile_number_view(corresponding_profile),
                            extensions: owned_extensions_view(extensions), next_tlm,
                        }
                    """,
                    "main_header_fields_view": """
                        crate::specs::Part1LayoutMainFields {
                            image_size: parsed_image_size_view(size), coding_style: parsed_coding_style_view(style),
                            quantization: quantization_view(quantization), styles: component_style_owner_view(styles),
                            quantizations: parsed_quantization_owner_view(quantizations),
                            roi: roi_shifts_view(roi), progression: progression_changes_view(progression),
                            transform: match transform {
                                None => None, Some(transform) => Some(multiple_component_transform_view(transform)),
                            },
                            extensions: owned_extensions_view(extensions), r_siz,
                            capabilities: optional_capabilities_view(capabilities),
                            profile: optional_profile_number_view(profile),
                            corresponding_profile: optional_profile_number_view(corresponding_profile), segments,
                        }
                    """,
                    "layout_main_header_outcome": """
                        match result {
                            Err(error) => Err(error),
                            Ok(layout) => {
                                let info = layout.info;
                                Ok(main_header_fields_view(&info.image_size, info.coding_style, &info.quantization,
                                    &info.component_coding_styles, &info.component_quantizations, &info.roi_shifts,
                                    &info.progression_changes, &info.multiple_component_transform, &info.part2_extensions,
                                    info.profile.r_siz, &info.profile.extended_capabilities, &info.profile.profile,
                                    &info.profile.corresponding_profile, info.main_header_segments))
                            },
                        }
                    """,
                })
            text = source_text(path)
            for name, expected_body in projections.items():
                projection_headers = list(re.finditer(
                    r"(?m)^([ \t]*)pub\(crate\)[ \t]+closed[ \t]+spec[ \t]+fn[ \t]+"
                    + re.escape(name) + r"\b", text,
                ))
                projection = (_coverage_function_body(text, projection_headers[0])
                              if len(projection_headers) == 1 else None)
                if projection is None or re.sub(r"\s+", "", projection) != re.sub(r"\s+", "", expected_body):
                    label = "whole raw main-header Result" if main_header else "whole profile Result"
                    raise ValueError(f"{label} requires complete raw projection: {name}")
        if entry["id"] == "part1-complete-native-raw-main-header-result":
            models = {
                "part1_main_header_initial", "part1_main_header_payload", "part1_main_header_mct_payload",
                "part1_main_header_extension_payload", "part1_main_header_after_components",
                "part1_main_header_after_depths", "part1_finish_main_header",
                "part1_main_header_continuation", "part1_read_main_header", "part1_main_header_fields",
                "part1_main_header_layout_relation",
            }
            if not {("specs/main_header.rs", name) for name in models}.issubset(
                {(ref["path"], ref["symbol"]) for ref in entry["spec_refs"]}
            ):
                raise ValueError("whole raw main-header Result model must bind the complete source-derived chain")
            path = (ROOT / _MAIN_HEADER_LAYOUT[0]).resolve()
            body = _coverage_function_body(source_text(path), function_header(path, _MAIN_HEADER_LAYOUT[1]))
            public = {"path": _MAIN_HEADER_LAYOUT[0], "symbol": "parse_layout"}
            public_body = (_coverage_function_body(source_text(path), function_header(path, public["symbol"]))
                           if public in entry["implementation_refs"] else None)
            if public_body is None or re.fullmatch(_RAW_LAYOUT_WRAPPER_BODY, public_body) is None:
                raise ValueError("whole raw main-header Result not used by claimed implementation: actual raw wrapper")
            raw_view = _coverage_call("main_header_accumulator_view", *_MAIN_HEADER_RAW_ARGUMENTS)
            continuation = _coverage_call("crate::specs::part1_main_header_continuation",
                                         _coverage_call("parser_view", r"&\s*parser"), raw_view, "input_length")
            finish = _coverage_call("crate::specs::part1_finish_main_header",
                                   _coverage_call("parser_view", r"&\s*parser"), raw_view)
            initial_reader = _coverage_call("parser_view", r"&\s*self")
            root = _coverage_call("crate::specs::part1_read_main_header", "initial_reader")
            if body is None or any(re.search(pattern, body) is None for pattern in (
                r"let\s+ghost\s+initial_reader\s*=\s*" + initial_reader + r"\s*;",
                r"let\s+ghost\s+main_goal\s*=\s*" + root + r"\s*;",
                r"let\s+ghost\s+main_initial\s*=\s*" + raw_view + r"\s*;",
                r"let\s+ghost\s+raw_main\s*=\s*" + raw_view + r"\s*;",
                r"verus_spec\s*\(\s*invariant\s+initial_reader\s*==\s*" + initial_reader
                + r"\s*,\s*main_goal\s*==\s*" + root + r"\s*,\s*main_goal\s*==\s*" + continuation
                + r"\s*,(?:\s*input_length\s*==\s*"
                + _coverage_call("crate::specs::part1_parse_layout_prologue", "initial_reader")
                + r"\s*\.\s*1\s*\.\s*input\s*\.\s*len\s*\(\s*\)\s+as\s+usize\s*,)?"
                + r"\s*ensures\s+main_goal\s*==\s*" + finish,
            )):
                raise ValueError("whole raw main-header Result requires actual raw initialization, traversal and finalization state")
            completed = """
                let ghost complete_main = crate::specs::Part1MainHeader {
                    reader: parser_view(&parser),
                    raw: crate::specs::Part1MainHeaderAccumulator {
                        image_size: parsed_image_size_view(&image_size), ..depth_main
                    },
                    end: main_header_end, header: main_header@, ppm_frames: packed_header_frames_view(ppm_frames@),
                    coding_style: parsed_coding_style_view(coding_style), quantization: quantization_view(&quantization),
                    styles: component_style_owner_view(&component_coding_styles),
                    quantizations: parsed_quantization_owner_view(&component_quantizations),
                    mct: mct_parameters_view(&main_mct_parameters),
                    transform: match multiple_component_transform {
                        None => None, Some(transform) => Some(multiple_component_transform_view(&transform)),
                    },
                    tile_count,
                };
            """
            checkpoint = """
                proof! {
                    reveal(mct_parameters_view);
                    reveal(mct_graph_outcome);
                    reveal(selection_geometry_view);
                    reveal(parsed_image_size_view);
                    assert(main_goal == Ok(complete_main));
                    reveal(main_header_fields_view);
                    assert(crate::specs::part1_main_header_fields(complete_main) == main_header_fields_view(
                        &image_size, coding_style, &quantization, &component_coding_styles, &component_quantizations,
                        &roi_shifts, &progression_changes, &multiple_component_transform, &part2_extensions,
                        r_siz, &extended_capabilities, &profile, &corresponding_profile, main_header_segments));
                }
            """
            canonical_body = re.sub(r"\s+", "", body)
            if any(re.sub(r"\s+", "", fragment) not in canonical_body for fragment in (completed, checkpoint)):
                raise ValueError("whole raw main-header Result requires complete actual reader/owner output and unconditional cut")
        if entry["id"] == "part1-complete-native-persistent-tile-state-fold":
            layout = {"path": "src/codestream/layout.rs", "symbol": "Parser::parse_layout"}
            if layout not in entry["implementation_refs"]:
                raise ValueError("persistent fold not used by claimed implementation: actual layout required")
            path = (ROOT / layout["path"]).resolve()
            body = _coverage_function_body(source_text(path), function_header(path, layout["symbol"]))
            if body is None:
                raise ValueError("persistent fold requires actual layout body")
            view = _coverage_call(
                "persistent_tile_state_view", *(name + r"\s*@" for name in _PERSISTENT_TILE_STATE_FIELDS),
            )
            fold = _coverage_call(
                "crate::specs::part1_persistent_tile_state_fold",
                "initial_persistent_state", "persistent_commits",
            )
            successful = r"\(\s*" + _coverage_call("Ok", r"\(\s*\)") + r"\s*,\s*" + view + r"\s*\)"
            initialization = (
                r"let\s+ghost\s+initial_persistent_state\s*=\s*" + view + r"\s*;\s*"
                r"let\s+ghost\s+mut\s+persistent_commits\s*:\s*Seq\s*<\s*"
                r"crate::specs::Part1PersistentTileCommit\s*>\s*=\s*Seq::empty\s*\(\s*\)\s*;"
            )
            invariant = r"verus_spec\s*\(\s*invariant\s+" + fold + r"\s*==\s*" + successful
            if (re.search(initialization, body) is None
                    or re.search(invariant, body) is None
                    or re.search(_coverage_call(
                        "assert", r"initial_persistent_state\s*==\s*"
                        + _coverage_call("crate::specs::part1_empty_persistent_tile_state", "tile_state_count"),
                    ), body) is None):
                raise ValueError("persistent fold requires complete empty initialization and loop invariant")
            snapshot = (
                r"let\s+ghost\s+previous_persistent_state\s*=\s*" + view + r"\s*;\s*"
                r"let\s+ghost\s+persistent_commit\s*=\s*crate::specs::Part1PersistentTileCommit\s*\{\s*"
                r"position\s*:\s*parser\.position\s*,\s*start\s*:\s*tile_part\.start\s*,\s*"
                r"index\s*:\s*tile_index\s*,\s*previous_roi\s*:\s*"
                + _coverage_call("optional_roi_shifts_view", "previous_roi_shifts")
                + r"\s*,\s*payload\s*:\s*" + _coverage_call("tile_part_payload_view", r"&\s*payload")
                + r"\s*,\s*parameters\s*:\s*" + _coverage_call("mct_parameter_copy_view", r"&\s*tile_parameters")
                + r"\s*,\s*extensions\s*:\s*" + _coverage_call("owned_extensions_view", r"&\s*tile_extensions")
                + r"\s*,?\s*\}\s*;"
            )
            captured = re.search(snapshot, body)
            handoff = re.search(
                r"\blet\s*\(\s*payload\s*,\s*tile_parameters\s*,\s*tile_extensions\s*\)\s*=\s*"
                r"parser\s*\.\s*read_tile_part\s*\(", body,
            )
            six_commit = re.search(r"\bparser\s*\.\s*commit_persistent_tile_configuration\s*\(", body)
            if (captured is None or handoff is None or six_commit is None
                    or not handoff.start() < captured.start() < six_commit.start()):
                raise ValueError("persistent fold requires actual reader-derived complete commit snapshot")
            stores = []
            for states, owner in (("tile_mct_parameters", "tile_parameters"),
                                   ("tile_part2_extensions", "tile_extensions")):
                stores.append(
                    r"\*\s*" + states + r"\s*\.\s*" + _coverage_call("get_mut", "tile_index")
                    + r"\s*\.\s*" + _coverage_call(
                        "ok_or_else", r"\|\|\s*" + _coverage_call(
                            "parser.malformed_here", "MalformedKind::InvalidTilePart"),
                    ) + r"\s*\?\s*=\s*" + _coverage_call("Some", owner) + r"\s*;"
                )
            step = _coverage_call(
                "crate::specs::part1_commit_persistent_tile_state",
                "previous_persistent_state", "persistent_commit",
            )
            checkpoint = (
                r"\s*".join(stores) + r"\s*" + _coverage_call("tile_part_payloads.push", "payload")
                + r"\s*;\s*#\[\s*cfg\s*\(\s*verus_keep_ghost\s*\)\s*\]\s*proof!\s*\{\s*"
                + r"\s*".join(_coverage_call("reveal", name) + r"\s*;" for name in (
                    "persistent_tile_state_view", "persistent_tile_configuration_view",
                    "super::persistent_tile_configuration_sequences_view",
                    "crate::specs::part1_commit_persistent_tile_state",
                ))
                + r"\s*" + _coverage_call("assert", step + r"\s*==\s*" + successful) + r"\s*;\s*"
                r"persistent_commits\s*=\s*persistent_commits\.push\s*\(\s*persistent_commit\s*\)\s*;\s*"
                + _coverage_call("assert", r"persistent_commits\.drop_last\s*\(\s*\)\s*==\s*previous_persistent_commits") + r"\s*;\s*"
                + _coverage_call("assert", r"persistent_commits\.last\s*\(\s*\)\s*==\s*persistent_commit") + r"\s*;\s*"
                + _coverage_call("reveal", "crate::specs::part1_persistent_tile_state_fold") + r"\s*;\s*"
                + _coverage_call("assert", fold + r"\s*==\s*" + successful) + r"\s*;"
            )
            if re.search(checkpoint, body[six_commit.start():]) is None:
                raise ValueError("persistent fold requires ordered actual stores/append and unconditional complete checkpoints")
            projections = {
                "persistent_tile_state_view": """
                    (persistent_tile_configuration_sequences_view(
                        roi, styles, quantizations, style_parts, component_quantizations, progression),
                     parameters.map_values(|value: Option<MctParameters>| match value {
                         None => None, Some(owner) => Some(mct_parameter_copy_view(&owner)),
                     }),
                     extensions.map_values(|value: Option<Part2Extensions>| match value {
                         None => None, Some(owner) => Some(owned_extensions_view(&owner)),
                     }),
                     payloads.map_values(|value: TilePartPayload<'_>| tile_part_payload_view(&value)),)
                """,
                "persistent_tile_configuration_view": """
                    persistent_tile_configuration_sequences_view(
                        roi@, styles@, quantizations@, style_parts@, component_quantizations@, progression@)
                """,
                "persistent_tile_configuration_sequences_view": """
                    (roi.map_values(|value: Option<RoiShifts>| match value {
                        None => None, Some(shifts) => Some(roi_shifts_view(&shifts)),
                     }),
                     styles.map_values(|value: Option<CodingStyle>| match value {
                        None => None, Some(style) => Some(parsed_coding_style_view(style)),
                     }),
                     quantizations.map_values(|value: Option<Quantization>| match value {
                        None => None, Some(quantization) => Some(quantization_view(&quantization)),
                     }),
                     style_parts,
                     component_quantizations.map_values(|value: Option<ComponentQuantizations>| match value {
                        None => None, Some(owner) => Some(parsed_quantization_owner_view(&owner)),
                     }),
                     progression.map_values(|value: Option<ProgressionChanges>| match value {
                        None => None, Some(changes) => Some(progression_changes_view(&changes)),
                     }),)
                """,
            }
            path = (ROOT / "src/codestream/persistent_tile_configuration_proof_support.rs").resolve()
            for name, expected in projections.items():
                text = source_text(path)
                projection_headers = list(re.finditer(
                    r"(?m)^([ \t]*)pub\(crate\)[ \t]+closed[ \t]+spec[ \t]+fn[ \t]+"
                    + re.escape(name) + r"\b", text,
                ))
                projection = (_coverage_function_body(text, projection_headers[0])
                              if len(projection_headers) == 1 else None)
                if projection is None or re.sub(r"\s+", "", projection) != re.sub(r"\s+", "", expected):
                    raise ValueError(f"persistent fold requires complete physical projection: {name}")
        if entry["id"] == "part1-complete-native-owned-tile-inheritance":
            layout = {"path": "src/codestream/layout.rs", "symbol": "Parser::parse_layout"}
            if layout not in entry["implementation_refs"]:
                raise ValueError("owned inheritance not used by claimed implementation: actual layout required")
            layout_path = (ROOT / layout["path"]).resolve()
            body = _coverage_function_body(source_text(layout_path), function_header(layout_path, layout["symbol"]))
            if body is None or len(re.findall(r"\binherited_tile_owner\s*\(", body)) != 4:
                raise ValueError("owned inheritance requires all four actual borrowed choices")
            previous_end = 0
            checkpoints = []
            for local, main, states, view in _OWNED_TILE_INHERITANCE_FIELDS:
                pattern = (
                    r"\blet\s+" + local + r"\s*=\s*"
                    + _coverage_call("inherited_tile_owner", "tile_index",
                                     r"&\s*" + main, r"&\s*" + states + r"\s*,?")
                    + r"\s*\.\s*" + _coverage_call("clone") + r"\s*;"
                )
                match = re.search(pattern, body)
                if match is None or match.start() < previous_end:
                    raise ValueError(f"owned inheritance clone/source/order mismatch: {local}")
                previous_end = match.end()
                checkpoints.append(_coverage_call(
                    "assert",
                    _coverage_call(view, r"&\s*" + local) + r"\s*==\s*"
                    + _coverage_call(view, r"&\s*" + _coverage_call(
                        "crate::specs::part1_inherited_tile_owner", "tile_index", main, states + r"\s*@",
                    )),
                ) + r"\s*;")
            handoff = re.search(
                r"\blet\s*\(\s*payload\s*,\s*tile_parameters\s*,\s*tile_extensions\s*\)\s*=\s*"
                r"parser\s*\.\s*read_tile_part\s*\(", body,
            )
            proof = (
                r"\s*#\[\s*cfg\s*\(\s*verus_keep_ghost\s*\)\s*\]\s*proof!\s*\{\s*"
                + _coverage_call("reveal", r"crate::specs::part1_inherited_tile_owner") + r"\s*;\s*"
                + r"\s*".join(checkpoints) + r"\s*\}\s*"
            )
            if handoff is None or handoff.start() < previous_end or re.fullmatch(
                proof, body[previous_end:handoff.start()],
            ) is None:
                raise ValueError("owned inheritance requires four unconditional complete cloned-view checkpoints")
        if entry["id"] == "part1-complete-native-mct-parameter-clone":
            layout = {"path": "src/codestream/layout.rs", "symbol": "Parser::parse_layout"}
            if layout not in entry["implementation_refs"]:
                raise ValueError("MCT clone not used by claimed implementation: actual layout required")
            for path, symbol, pattern in _MCT_PARAMETER_CLONE_CONSUMERS:
                consumer_path = (ROOT / path).resolve()
                text = source_text(consumer_path)
                body = _coverage_function_body(text, function_header(consumer_path, symbol))
                if body is None or re.search(pattern, body) is None:
                    raise ValueError(f"MCT clone not used by claimed implementation: typed edge {symbol}")
            text = source_text((ROOT / "src/codestream/proof_support.rs").resolve())
            projection_headers = list(re.finditer(
                r"(?m)^([ \t]*)pub[ \t]+closed[ \t]+spec[ \t]+fn[ \t]+mct_parameter_copy_view\b",
                text,
            ))
            body = (
                _coverage_function_body(text, projection_headers[0])
                if len(projection_headers) == 1 else None
            )
            complete = (
                r"\s*let\s+complete\s*=\s*" + _coverage_call("mct_parameters_view", "value")
                + r"\s*;\s*\(\s*complete\.arrays\s*,\s*complete\.records\s*,\s*complete\.order\s*\)\s*"
            )
            if body is None or re.fullmatch(complete, body) is None:
                raise ValueError("MCT clone copy projection must retain all physical fields")
        if entry["id"] in ids:
            raise ValueError(f"duplicate normative inventory id: {entry['id']}")
        ids.add(entry["id"])
        for field in (
            "implementation_refs", "spec_refs", "contract_refs",
            "proof_refs", "test_refs",
        ):
            for reference in entry[field]:
                path = (ROOT / reference["path"]).resolve()
                if not path.is_relative_to(ROOT.resolve()) or not path.is_file():
                    raise ValueError(f"missing normative evidence path: {reference['path']}")
                if path not in symbols:
                    # Look ahead so `const fn name` indexes both overlapping declarations.
                    symbols[path] = set(re.findall(
                        r"\b(?:fn|struct|enum|type|const|trait)\s+(?=([A-Za-z_][A-Za-z0-9_]*)\b)",
                        source_text(path),
                    ))
                short = reference["symbol"].rsplit("::", 1)[-1]
                present = (short in symbols[path] if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", short)
                           else _coverage_symbol_present(path, reference["symbol"], text=source_text(path)))
                if not present:
                    raise ValueError(
                        f"missing normative evidence symbol: {reference['path']}::{reference['symbol']}"
                    )
        spec_symbols = {reference["symbol"] for reference in entry["spec_refs"]}
        proved_apis = [
            reference for reference in entry["proof_refs"]
            if ((reference["path"], reference["symbol"]) in (
                _PACKET_PROVED_BOUNDARY_APIS | _RECONSTRUCTION_PROVED_BOUNDARY_APIS
                | _RESOLUTION_GEOMETRY_PROVED_BOUNDARY_APIS
                | _SUBBAND_ADMISSION_PROVED_BOUNDARY_APIS
                | _SUBBAND_VECTOR_PROVED_BOUNDARY_APIS
            ) or (entry["id"] == _RAW_JPX_INSPECTION_ENTRY
                  and (reference["path"], reference["symbol"]) in _RAW_JPX_INSPECTION_APIS)
              or (entry["id"] == _RAW_RENDER_ENTRY
                  and (reference["path"], reference["symbol"]) in _RAW_RENDER_APIS)
              or (entry["id"] == _RAW_COMPOSITION_RENDER_ENTRY
                  and (reference["path"], reference["symbol"]) in _RAW_COMPOSITION_RENDER_APIS)
              or (entry["id"] == _RAW_CONTAINER_IMAGE_ENTRY
                  and (reference["path"], reference["symbol"]) in _RAW_CONTAINER_IMAGE_APIS)
              or (entry["id"] == _RAW_CONTAINER_COLOR_ENTRY
                  and (reference["path"], reference["symbol"]) in _RAW_CONTAINER_COLOR_APIS)
              or (entry["id"] == _RAW_JPX_PUBLIC_IMAGE_ENTRY
                  and (reference["path"], reference["symbol"]) in _RAW_JPX_PUBLIC_IMAGE_APIS)
              or (entry["id"] == _JPIP_MESSAGE_ENTRY
                  and (reference["path"], reference["symbol"]) in _JPIP_MESSAGE_BOUNDARIES)
              or (entry["id"] == _JPIP_LAYOUT_ENTRY
                  and (reference["path"], reference["symbol"]) in _JPIP_LAYOUT_APIS)
              or (entry["id"] == _JPIP_RESPONSE_ENTRY
                  and (reference["path"], reference["symbol"]) in _JPIP_RESPONSE_APIS)
              or (entry["id"] == _JPIP_RANGE_ENTRY
                  and (reference["path"], reference["symbol"]) in _JPIP_RANGE_APIS)
              or (entry["id"] == _JPIP_PLANNED_ENTRY
                  and (reference["path"], reference["symbol"]) in _JPIP_PLANNED_APIS)
              or (entry["id"] == _JPIP_TRANSCODE_ENTRY
                  and (reference["path"], reference["symbol"]) in _JPIP_TRANSCODE_APIS)
              or (entry["id"] == _JPIP_PROGRESSIVE_ENTRY
                  and (reference["path"], reference["symbol"]) in _JPIP_PROGRESSIVE_APIS)
              or (entry["id"] == _JPIP_TRANSITION_ENTRY
                  and (reference["path"], reference["symbol"]) in _JPIP_TRANSITION_APIS))
            and reference not in entry["contract_refs"]
        ]
        for reference in [*entry["contract_refs"], *proved_apis]:
            claimed_consumer = reference in entry["contract_refs"]
            path = (ROOT / reference["path"]).resolve()
            text = source_text(path)
            short = reference["symbol"].rsplit("::", 1)[-1]
            signature_match = function_header(path, reference["symbol"])
            if signature_match is None:
                raise ValueError(f"missing linked contract function: {short}")
            signature = text.find("fn", signature_match.start(), signature_match.end())
            contract_start = text.rfind("#[cfg_attr", 0, signature)
            contract = text[contract_start:signature] if contract_start >= 0 else ""
            body_start = text.find("{", signature)
            if body_start < 0:
                raise ValueError(f"linked contract function lacks an executable body: {short}")
            mutating = re.search(r"&\s*(?:'\w+\s+)?mut\b", text[signature:body_start]) is not None
            mutable_parameters = set(re.findall(
                r"\b(\w+)\s*:\s*&\s*(?:'\w+\s+)?mut\b", text[signature:body_start],
            ))
            if re.search(r"&\s*(?:'\w+\s+)?mut\s+self\b", text[signature:body_start]):
                mutable_parameters.add("self")
            bundle = (reference["path"], reference["symbol"]) == ("src/packet/multi_packet.rs", "decode_multi_code_block_packet")
            if bundle:
                bundle_source = source_text((ROOT / "src/packet.rs").resolve())
                bundle_definition = re.search(r"\bstruct\s+PacketCodeBlockExecution\b[^{]*\{([^}]*)\}", bundle_source)
                bundle_fields = set(re.findall(
                    r"\b(\w+)\s*:\s*&\s*(?:'\w+\s+)?mut\b", bundle_definition[1],
                )) if bundle_definition else set()
                if (bundle_fields != _PACKET_EXECUTION_BUNDLE_FIELDS
                        or re.search(r"\bexecution\s*:\s*PacketCodeBlockExecution\s*<\s*'_\s*>",
                                     text[signature:body_start]) is None):
                    raise ValueError(f"linked function lacks executable Verus contract: {short}; unknown execution bundle")
                mutable_parameters.update("execution." + name for name in bundle_fields)
                mutating = True
            named_prefix = r"\bverus_spec\(\s*(\w+)\s*=>\s*(?:requires\b[\s\S]*?)?ensures\s+"
            model_suffix = r"\s*==\s*crate::specs::(?P<model>\w+)\s*\("
            scalar_result = re.search(named_prefix + r"\1(?:\s+as\s+nat)?" + model_suffix, contract)
            result_projection = {
                ("src/jpx/channels.rs", "layer_channels"): "layer_channels_outcome",
                ("src/jpx/layer_decode.rs", "owned_layer_from_image"): "owned_layer_outcome",
                ("src/jpx/render.rs", "render_decoded_layers"): "crate::color::converted_image_result",
                ("src/jpx/timeline.rs", "select_frame_instructions"): "frame_selection_result",
                ("src/jpx/timeline.rs", "build_timeline"): "timeline_frames_result",
                ("src/jpx/render.rs", "render_normalized_frame"): "crate::color::converted_image_result",
                ("src/color/output.rs", "from_layer"): "converted_image_result",
                ("src/color/output.rs", "from_composited"): "converted_image_result",
                ("src/color/normalization.rs", "normalize_component"): "normalized_plane_result",
                ("src/color/admission.rs", "channel_layout"): "channel_layout_result",
                ("src/tier1/raw.rs", "raw_reader_from_input"): "raw_reader_outcome",
                ("src/transform/quantization.rs", "inverse_quantize_values"): "reconstruction_outcome",
                ("src/transform/quantization.rs", "inverse_quantize"): "reconstruction_outcome",
                ("src/transform/quantization.rs", "inverse_quantize_magnitudes"): "reconstruction_outcome",
                ("src/transform/quantization.rs", "inverse_quantize_plane"): "reconstruction_outcome",
                ("src/transform/wavelets.rs", "inverse_5_3"): "sequence_outcome",
                ("src/transform/wavelets.rs", "inverse_9_7"): "sequence_outcome",
                ("src/transform/levels.rs", "inverse_horizontal_5_3"): "reconstruction_outcome",
                ("src/transform/levels.rs", "inverse_horizontal_9_7"): "reconstruction_outcome",
                ("src/transform/levels.rs", "inverse_vertical_5_3"): "reconstruction_outcome",
                ("src/transform/levels.rs", "inverse_vertical_9_7"): "reconstruction_outcome",
                ("src/transform/levels.rs", "inverse_level_5_3"): "reconstruction_outcome",
                ("src/transform/levels.rs", "inverse_level_9_7"): "reconstruction_outcome",
                ("src/transform/output.rs", "convert_samples"): "sequence_outcome",
                ("src/transform/wavelets.rs", "interleave"): "sequence_outcome",
                ("src/tier1/ht_cleanup_readers.rs", "ht_mel_from_input"): "ht_mel_outcome",
                ("src/tier1/ht_cleanup_readers.rs", "ht_reverse_vlc_from_input"): "ht_reverse_vlc_outcome",
                ("src/tier1/ht_cleanup_readers.rs", "ht_cleanup_readers_from_inputs"): "ht_cleanup_readers_outcome",
                ("src/tier1/ht_cleanup_readers.rs", "ht_magsgn_from_input"): "ht_magsgn_outcome",
                ("src/tier1/ht_refinement_readers.rs", "ht_forward_refinement_from_input"): "ht_forward_refinement_outcome",
                ("src/tier1/ht_refinement_readers.rs", "ht_reverse_refinement_from_input"): "ht_reverse_refinement_outcome",
                ("src/tier1/ht_refinement_readers.rs", "ht_refinement_readers_from_inputs"): "ht_refinement_readers_outcome",
                ("src/tier1/ht_segments.rs", "parse_ht_block_segments"): "ht_block_segments_outcome",
                ("src/tier1/ht_metadata.rs", "decode_ht_cleanup_segment_metadata"): "ht_cleanup_metadata_outcome",
                ("src/tier1/ht_cleanup.rs", "reconstruct_ht_cleanup_plane"): "ht_plane_outcome",
                ("src/tier1/ht_cleanup.rs", "prepare_ht_cleanup_symbols"): "ht_cleanup_prepare_outcome",
                ("src/tier1/state.rs", "duplicate"): "code_block_plane_outcome",
                ("src/tier1/ht_refinement.rs", "decode_ht_refinement_plane"): "ht_plane_outcome",
                ("src/tier1/ht_refinement.rs", "run_ht_significance_stripe"): "ht_sigprop_plane_outcome",
                ("src/tier1/ht_refinement.rs", "run_ht_significance_pass"): "ht_sigprop_plane_outcome",
                ("src/tier1/ht_refinement.rs", "ht_significance_magnitude"): "ht_refinement_magnitude_outcome",
                ("src/tier1/ht_refinement.rs", "ht_refinement_delta"): "ht_refinement_magnitude_outcome",
                ("src/tier1/ht_refinement.rs", "ht_collect_cleanup_significance"): "ht_boolean_vector_view",
                ("src/tier1/ht_refinement.rs", "copy_ht_refinement_bytes"): "ht_byte_vector_outcome",
                ("src/tier1/state.rs", "code_block_plane_from_dimensions"): "code_block_plane_outcome",
                ("src/tier1/state.rs", "coefficient_from_magnitude"): "coefficient_raw_outcome",
                ("src/tier1/state.rs", "coefficient"): "coefficient_raw_outcome",
                ("src/tier1/state.rs", "signed_magnitude"): "coefficient_signed_outcome",
                ("src/tier1/state.rs", "coefficients"): "coefficient_slice_view",
                ("src/tier1/state.rs", "wide_magnitude"): "crate::magnitude::magnitude_limbs",
                ("src/color/conversion.rs", "convert_jp2_color"): "converted_image_result",
                ("src/color/conversion.rs", "convert_color_channel"): "converted_channel_result",
                ("src/color/conversion.rs", "convert_alpha_channel"): "converted_channel_result",
                ("src/color/crop.rs", "crop"): "converted_image_result",
                ("src/color/crop.rs", "crop_plane"): "normalized_plane_result",
                ("src/decode/output.rs", "convert_selected_color"): "crate::color::converted_image_result",
                ("src/decode/reconstruction.rs", "prepare_tile_component"): "prepared_component_outcome",
                ("src/decode/reconstruction.rs", "initialize_prepare_working"): "prepare_working_outcome",
                ("src/decode/reconstruction.rs", "collect_prepare_coefficients"): "crate::transform::quantized_coefficients_outcome",
                ("src/decode/reconstruction.rs", "collect_prepare_cell"): "prepare_cell_outcome",
                ("src/decode/reconstruction.rs", "copy_prepare_plane"): "prepare_fold_outcome",
                ("src/decode/reconstruction.rs", "finish_prepared_component"): "prepared_component_outcome",
                ("src/decode/reconstruction.rs", "as_tile_component"): "crate::image::assembly_tile_view",
                ("src/decode/output.rs", "copy_typed_component"): "crate::image::typed_component_output",
                ("src/decode/output.rs", "map_palette_component"): "crate::image::typed_component_output",
                ("src/decode/output.rs", "apply_jp2_output"): "crate::image::decoded_typed_image_outcome",
                ("src/image/layout.rs", "typed_component_from_parts"): "typed_component_value_view",
                ("src/image/layout.rs", "typed_image_from_components_with_origin"): "decoded_typed_image_outcome",
                ("src/image/assembly.rs", "assemble_image"): "decoded_image_outcome",
                ("src/image/assembly.rs", "assemble_selected_image"): "decoded_image_outcome",
                ("src/image/samples.rs", "typed_samples"): "decoded_typed_samples_outcome",
                ("src/image/samples.rs", "typed"): "decoded_typed_image_outcome",
                ("src/packet/precinct.rs", "decoder"): "packet_decoder_outcome",
            }.get((reference["path"], short))
            if (reference["path"], reference["symbol"]) == ("src/image/layout.rs", "TypedImage::component"):
                result_projection = "typed_component_reference_output"
            expected_result_model = {
                ("src/jp2/color.rs", "value"): "part2_palette_value",
                ("src/jp2/color.rs", "palette_value_error"): "part2_composition_error",
                ("src/image/samples.rs", "typed_samples"): "part1_decoded_component_typed_samples",
                ("src/image/samples.rs", "typed"): "part1_decoded_image_typed",
                ("src/packet/precinct.rs", "decoder"): "part1_packet_precinct_decoder",
                ("src/image/assembly.rs", "assemble_image"): "part1_assemble_image",
                ("src/image/assembly.rs", "assemble_selected_image"): "part1_assemble_selected_image",
                ("src/tier1/ht_segments.rs", "parse_ht_block_segments"): "ht_parse_block_segments",
                ("src/tier1/ht_metadata.rs", "decode_ht_cleanup_segment_metadata"): "ht_cleanup_segment_metadata",
                ("src/tier1/ht_cleanup.rs", "reconstruct_ht_magnitude"): "ht_reconstruct_numeric_magnitude",
                ("src/tier1/ht_cleanup.rs", "reconstruct_ht_cleanup_plane"): "ht_cleanup_plane",
                ("src/tier1/ht_cleanup.rs", "prepare_ht_cleanup_symbols"): "ht_cleanup_prepare",
                ("src/tier1/ht_contributions.rs", "store_ht_coefficient_symbols"): "ht_store_coefficient_symbols",
                ("src/tier1/state.rs", "duplicate"): "tier1_duplicate_plane",
                ("src/tier1/ht_refinement.rs", "decode_ht_refinement_plane"): "ht_refinement_plane",
                ("src/tier1/ht_refinement.rs", "magnitude_sample"): "ht_magref_sample",
                ("src/tier1/ht_refinement.rs", "magnitude_column"): "ht_magref_rows",
                ("src/tier1/ht_refinement.rs", "magnitude_stripe"): "ht_magref_columns",
                ("src/tier1/ht_refinement.rs", "magnitude_pass"): "ht_magref_stripes",
                ("src/tier1/ht_refinement.rs", "discover_sample"): "ht_discover_sample",
                ("src/tier1/ht_refinement.rs", "discover_column"): "ht_discovery_rows",
                ("src/tier1/ht_refinement.rs", "discover_patch"): "ht_discovery_columns",
                ("src/tier1/ht_refinement.rs", "sign_sample"): "ht_patch_sign_sample",
                ("src/tier1/ht_refinement.rs", "signs"): "ht_pending_signs",
                ("src/tier1/ht_refinement.rs", "run_ht_significance_stripe"): "ht_sigprop_patches",
                ("src/tier1/ht_refinement.rs", "run_ht_significance_pass"): "ht_sigprop_stripes",
                ("src/tier1/ht_refinement.rs", "ht_significance_magnitude"): "ht_significance_magnitude",
                ("src/tier1/ht_refinement.rs", "ht_refinement_delta"): "ht_refinement_delta",
                ("src/tier1/ht_refinement.rs", "ht_collect_cleanup_significance"): "ht_cleanup_significance",
                ("src/tier1/state.rs", "apply_ht_refinement_decision"): "ht_apply_refinement",
                ("src/tier1/state.rs", "neighbor_summary_with_causality"): "ht_neighbors",
                ("src/tier1/state.rs", "accumulate_neighbor"): "ht_accumulate_neighbor",
                ("src/tier1/state.rs", "ht_neighbor_summary_zero"): "ht_neighbor_zero",
                ("src/tier1/state.rs", "significant_neighbor_count"): "ht_significant_neighbor_count",
                ("src/tier1/legacy_passes.rs", "refined"): "tier1_statistics_increment",
                ("src/tier1/ht_contributions.rs", "decode_high_throughput_segments"): "ht_decode_segments",
                ("src/tier1/ht_contributions.rs", "decode_ht_coefficient_symbols"): "ht_coefficient_symbols",
                ("src/tier1/ht_cleanup.rs", "ht_significant_bitplanes"): "ht_significant_bitplanes",
                ("src/tier1/coding.rs", "uses_high_throughput"): "ht_block_coding_enabled",
                ("src/tier1/ht_refinement.rs", "copy_ht_refinement_bytes"): "ht_copy_refinement_bytes",
                ("src/tier1/legacy_passes.rs", "merge"): "tier1_statistics_merge",
                ("src/tier1/state.rs", "code_block_plane_from_dimensions"): "tier1_empty_plane",
                ("src/tier1/state.rs", "coefficient_from_magnitude"): "tier1_coefficient_new_outcome",
                ("src/tier1/ht_cleanup.rs", "complete_ht_kappa"): "ht_complete_kappa",
                ("src/tier1/state.rs", "ht_statistics_zero"): "tier1_statistics_zero",
                ("src/tier1/state.rs", "width"): "tier1_raw_plane_width",
                ("src/tier1/state.rs", "height"): "tier1_raw_plane_height",
                ("src/tier1/state.rs", "coefficients"): "tier1_raw_plane_coefficients",
                ("src/tier1/state.rs", "coefficient"): "tier1_raw_plane_coefficient",
                ("src/tier1/state.rs", "index"): "tier1_raw_plane_index",
                ("src/tier1/state.rs", "wide_magnitude"): "tier1_coefficient_limbs",
                ("src/tier1/state.rs", "signed_magnitude"): "tier1_raw_signed_coefficient",
                ("src/tier1/legacy_passes.rs", "scanned"): "tier1_statistics_increment",
                ("src/tier1/legacy_passes.rs", "decoded_symbols"): "tier1_statistics_increment",
                ("src/tier1/legacy_passes.rs", "became_significant"): "tier1_statistics_increment",
                ("src/decode/output.rs", "convert_selected_color"): "color_convert_selected",
                ("src/decode/reconstruction.rs", "prepare_tile_component"): "part1_prepare_standard_component",
                ("src/decode/reconstruction.rs", "initialize_prepare_working"): "part1_prepare_init_prefix",
                ("src/decode/reconstruction.rs", "collect_prepare_coefficients"): "part1_prepare_collect_coefficients",
                ("src/decode/reconstruction.rs", "collect_prepare_cell"): "part1_prepare_signed_cell",
                ("src/decode/reconstruction.rs", "copy_prepare_plane"): "part1_prepare_copy_plane",
                ("src/decode/reconstruction.rs", "finish_prepared_component"): "part1_prepare_finish",
                ("src/decode/reconstruction.rs", "as_tile_component"): "part1_prepared_as_tile",
                ("src/decode/output.rs", "copy_typed_component"): "part2_typed_component_copy",
                ("src/decode/output.rs", "map_palette_component"): "part2_palette_component",
                ("src/decode/output.rs", "apply_jp2_output"): "part2_apply_output_header",
                ("src/decode/output.rs", "palette_modulus"): "part2_palette_modulus",
                ("src/decode/output.rs", "invalid_jp2_output"): "part2_color_input_error",
                ("src/image/layout.rs", "typed_component_from_parts"): "part2_typed_component_from_parts",
                ("src/image/layout.rs", "typed_image_from_components_with_origin"): "part2_typed_image_from_parts",
                ("src/color/crop.rs", "crop"): "color_crop_image",
                ("src/color/crop.rs", "crop_plane"): "color_crop_plane",
                ("src/color/crop.rs", "crop_sample"): "color_crop_sample",
                ("src/color/conversion.rs", "convert_jp2_color"): "color_convert_jp2",
                ("src/color/conversion.rs", "convert_color_channel"): "color_convert_channel",
                ("src/color/conversion.rs", "convert_alpha_channel"): "color_convert_alpha",
                ("src/color/conversion.rs", "convert_sycc_pixel"): "color_sycc_pixel",
                ("src/color/admission.rs", "validate_components"): "color_validate_components",
                ("src/color/admission.rs", "validate_component_index"): "color_validate_component_index",
                ("src/color/admission.rs", "validate_component"): "color_validate_component",
                ("src/color/admission.rs", "validate_output_size"): "color_validate_output_size",
            }.get((reference["path"], short))
            if (reference["path"], reference["symbol"]) == ("src/image/layout.rs", "TypedImage::component"):
                expected_result_model = "part2_typed_image_component"
            kernel_view = r"crate::codestream::raw_kernel_view\s*\(\s*\*\s*kernel\s*\)"
            kernel_step_view = r"crate::codestream::raw_kernel_step_view\s*\(\s*\*\s*step\s*\)"
            kernel_coefficient_view = r"crate::codestream::raw_kernel_coefficient_view\s*\(\s*coefficient\s*\)"
            kernel_option = r"crate::transform::arbitrary_kernel_option\s*\(\s*kernel\s*\)"
            decoded_cap = r"crate::limits::resource_decoded_bytes_limit\s*\(\s*limits\s*\)"
            arbitrary_contract = {
                ("src/transform/arbitrary.rs", "inverse_arbitrary"): (
                    "sequence_outcome", "part2_inverse_arbitrary",
                    r"low@\s*,\s*high@\s*,\s*low_pass_first\s*,\s*" + kernel_view,
                ),
                ("src/transform/levels.rs", "inverse_horizontal_arbitrary"): (
                    "reconstruction_outcome", "part2_atk_inverse_horizontal",
                    r"wavelet_band_view\s*\(\s*low\s*\)\s*,\s*wavelet_band_view\s*\(\s*high\s*\)\s*,\s*"
                    r"output_width\s*,\s*low_pass_first\s*,\s*!\s*" + kernel_view + r"\.0\s*,\s*" + kernel_view + r"\s*,\s*" + decoded_cap,
                ),
                ("src/transform/levels.rs", "inverse_vertical_arbitrary"): (
                    "reconstruction_outcome", "part2_atk_inverse_vertical",
                    r"wavelet_band_view\s*\(\s*low\s*\)\s*,\s*wavelet_band_view\s*\(\s*high\s*\)\s*,\s*"
                    r"output_height\s*,\s*low_pass_first\s*,\s*!\s*" + kernel_view + r"\.0\s*,\s*" + kernel_view + r"\s*,\s*" + decoded_cap,
                ),
                ("src/transform/levels.rs", "inverse_level_arbitrary"): (
                    "reconstruction_outcome", "part2_atk_inverse_level",
                    r"wavelet_level_view\s*\(\s*level\s*\)\s*,\s*!\s*" + kernel_view + r"\.0\s*,\s*" + kernel_view + r"\s*,\s*" + decoded_cap,
                ),
                ("src/transform/arbitrary.rs", "apply_arbitrary_steps"): (
                    None, "part2_atk_steps",
                    r"old\s*\(\s*output\s*\)@\s*,\s*" + kernel_view + r"\s*,\s*low_pass_first\s*,\s*" + kernel_view + r"\.6\.len\s*\(\s*\)",
                ),
                ("src/transform/arbitrary.rs", "apply_arbitrary_step"): (
                    None, "part2_atk_step",
                    r"old\s*\(\s*output\s*\)@\s*,\s*" + kernel_step_view + r"\s*,\s*" + kernel_view + r"\s*,\s*low_pass_first\s*,\s*update_odd",
                ),
                ("src/transform/arbitrary.rs", "arbitrary_reversible_target"): (
                    None, "part2_atk_reversible_target",
                    r"output@\s*,\s*target\s*,\s*" + kernel_step_view + r"\s*,\s*" + kernel_view + r"\s*,\s*low_pass_first",
                ),
                ("src/transform/arbitrary.rs", "arbitrary_irreversible_target"): (
                    None, "part2_atk_irreversible_target",
                    r"output@\s*,\s*target\s*,\s*" + kernel_step_view + r"\s*,\s*" + kernel_view + r"\s*,\s*low_pass_first",
                ),
                ("src/transform/arbitrary.rs", "lifting_source_sum"): (
                    None, "part2_atk_source_sum",
                    r"samples@\s*,\s*target\s*,\s*coefficient\s*,\s*offset\s*,\s*whole_sample_filter\s*,\s*whole_sample_extension\s*,\s*low_pass_first",
                ),
                ("src/transform/arbitrary.rs", "extended_sample"): (
                    None, "part2_atk_extended", r"samples@\s*,\s*original_index\s*,\s*whole_sample_extension",
                ),
                ("src/transform/coefficients.rs", "coefficient_integer"): (
                    None, "part2_atk_integer", kernel_coefficient_view + r"\s*,\s*coefficient_type",
                ),
                ("src/transform/coefficients.rs", "coefficient_fixed"): (
                    None, "part2_atk_fixed_coefficient", kernel_coefficient_view + r"\s*,\s*coefficient_type",
                ),
                ("src/transform/coefficients.rs", "bytes_to_u128"): (
                    None, "part2_atk_bytes_prefix", r"bytes@\s*,\s*16",
                ),
                ("src/transform/coefficients.rs", "binary_to_fixed"): (
                    None, "part2_atk_binary_format", r"bits\s*,\s*total_bits\s*,\s*exponent_bits\s*,\s*fraction_bits\s*,\s*bias",
                ),
                ("src/transform/coefficients.rs", "fixed_from_binary_q32"): (
                    None, "part2_atk_binary_q32", r"negative\s*,\s*significand\s*,\s*binary_exponent",
                ),
                ("src/transform/coefficients.rs", "fixed_mul_q32"): (
                    None, "part2_atk_fixed_mul", r"value\s*,\s*factor",
                ),
                ("src/transform/coefficients.rs", "fixed_div_q32"): (
                    None, "part2_atk_fixed_div", r"value\s*,\s*divisor",
                ),
                ("src/transform/coefficients.rs", "round_shift_i128"): (
                    None, "part2_atk_round_shift", r"value\s*,\s*shift",
                ),
                ("src/decode/reconstruction.rs", "prepare_tile_component_with_kernel"): (
                    "prepared_component_outcome", "part2_prepare_component",
                    r"prepare_plan_view\s*\(\s*plan\s*\)\s*,\s*prepare_precincts_view\s*\(\s*precincts@\s*\)\s*,\s*"
                    r"prepare_style_view\s*\(\s*coding_style\s*\)\s*,\s*" + kernel_option + r"\s*,\s*" + decoded_cap,
                ),
                ("src/decode/reconstruction.rs", "reconstruct_prepare_working"): (
                    "prepare_fold_outcome", "part2_prepare_reconstruct",
                    r"working_bands_view\s*\(\s*working@\s*\)\s*,\s*prepare_plan_view\s*\(\s*plan\s*\)\s*,\s*"
                    r"prepare_style_view\s*\(\s*coding_style\s*\)\s*,\s*reversible\s*,\s*" + kernel_option + r"\s*,\s*" + decoded_cap,
                ),
                ("src/decode/reconstruction.rs", "reconstruct_prepare_resolution"): (
                    "prepare_fold_outcome", "part2_prepare_resolution",
                    r"before@\s*,\s*working_bands_view\s*\(\s*working@\s*\)\s*,\s*plan\.subbands@\s*,\s*"
                    r"direction\s*,\s*reversible\s*,\s*" + kernel_option + r"\s*,\s*" + decoded_cap,
                ),
            }.get((reference["path"], reference["symbol"]))
            if arbitrary_contract:
                result_projection, expected_result_model = arbitrary_contract[:2]
            packet_decoder_old = r"crate::tier1::tier1_decoder_state\s*\(\s*old\(\s*decoder\s*\)\s*\)"
            packet_decoder_final = r"crate::tier1::tier1_decoder_state\s*\(\s*final\(\s*decoder\s*\)\s*\)"
            packet_contribution = r"code_block_contribution_view\s*\(\s*contribution\s*\)"
            packet_cap = r"crate::limits::resource_code_block_pass_limit\s*\(\s*limits\s*\)"
            packet_byte_cap = r"crate::limits::resource_code_block_byte_limit\s*\(\s*limits\s*\)"
            packet_input_cap = r"crate::limits::resource_input_byte_limit\s*\(\s*limits\s*\)"
            packet_work_cap = r"crate::limits::resource_work_limit\s*\(\s*limits\s*\)"
            packet_all_caps = packet_cap + r"\s*,\s*" + packet_byte_cap + r"\s*,\s*" + packet_input_cap + r"\s*,\s*" + packet_work_cap
            packet_ht_caps = packet_cap + r"\s*,\s*" + packet_byte_cap + r"\s*,\s*" + packet_work_cap
            packet_body_arguments = packet_decoder_old + r"\s*,\s*" + packet_contribution + r"\s*,\s*body@\s*,\s*"
            packet_contract = {
                "CodeBlockContribution::segment": (
                    "part1_code_block_segment", None,
                    r"code_block_contribution_view\s*\(\s*self\s*\)\s*,\s*index",
                ),
                "prepare_code_block_contribution_body": (
                    "part1_code_block_body_prepare", packet_decoder_final,
                    packet_decoder_old + r"\s*,\s*" + packet_contribution + r"\s*,\s*body@",
                ),
                "decode_legacy_code_block_segment": (
                    "part1_legacy_code_block_segment",
                    r"legacy_packet_progress_view\s*\(\s*final\(\s*decoder\s*\)\s*,\s*\*\s*final\(\s*segment_index\s*\)\s*,\s*"
                    r"\*\s*final\(\s*offset\s*\)\s*,\s*\*\s*final\(\s*decoded_passes\s*\)\s*\)",
                    r"legacy_packet_progress_view\s*\(\s*old\(\s*decoder\s*\)\s*,\s*\*\s*old\(\s*segment_index\s*\)\s*,\s*"
                    r"\*\s*old\(\s*offset\s*\)\s*,\s*\*\s*old\(\s*decoded_passes\s*\)\s*\)\s*,\s*"
                    + packet_contribution + r"\s*,\s*body@\s*,\s*" + packet_all_caps,
                ),
                "decode_legacy_code_block_contribution_body": (
                    "part1_legacy_code_block_body", packet_decoder_final, packet_body_arguments + packet_all_caps,
                ),
                "decode_ht_segment_route": (
                    "ht_packet_segment_route", packet_decoder_final,
                    packet_decoder_old + r"\s*,\s*body@\s*,\s*passes\s*,\s*" + packet_ht_caps,
                ),
                "decode_ht_segment_body": (
                    "ht_packet_segment_body",
                    packet_decoder_final + r"\s*,\s*\*\s*final\(\s*offset\s*\)\s*,\s*\*\s*final\(\s*decoded_passes\s*\)",
                    packet_decoder_old + r"\s*,\s*segment\s*,\s*body@\s*,\s*\*\s*old\(\s*offset\s*\)\s*,\s*"
                    r"\*\s*old\(\s*decoded_passes\s*\)\s*,\s*" + packet_ht_caps,
                ),
                "run_ht_contribution_segments": (
                    "ht_packet_body_run", packet_decoder_final + r"\s*,\s*ht_body_progress_view\s*\(\s*final\(\s*progress\s*\)\s*\)",
                    packet_body_arguments + r"ht_body_progress_view\s*\(\s*old\(\s*progress\s*\)\s*\)\s*,\s*" + packet_ht_caps,
                ),
                "decode_ht_contribution_segments": (
                    "ht_packet_body_segments", packet_decoder_final, packet_body_arguments + packet_ht_caps,
                ),
                "decode_code_block_contribution_body_staged": (
                    "part1_code_block_body_staged", packet_decoder_final, packet_body_arguments + packet_all_caps,
                ),
                "decode_code_block_contribution_body": (
                    "part1_code_block_body_transaction", packet_decoder_final, packet_body_arguments + packet_all_caps,
                ),
            }.get(reference["symbol"]) if (
                reference["path"] == "src/packet.rs" or reference["path"].startswith("src/packet/")
            ) else None
            if packet_contract:
                expected_result_model = packet_contract[0]
            selection_geometry = r"crate::codestream::selection_geometry_view\s*\(\s*size\s*\)"
            selection_view = r"crate::options::decode_selection_view\s*\(\s*selection\s*\)"
            selection_decoded_cap = r"crate::limits::resource_decoded_bytes_limit\s*\(\s*limits\s*\)"
            selection_work_cap = r"crate::limits::resource_work_limit\s*\(\s*limits\s*\)"
            selection_header = r"jp2::associated_header_option\s*\(\s*header\s*\)"
            selection_image = r"crate::image::typed_image_value_view\s*\(\s*\*\s*image\s*\)"
            selected_header_arguments = (
                r"header\.image\s*,\s*codestream\.image_size\.width\s*,\s*codestream\.image_size\.height\s*,\s*"
                r"codestream\.image_size\.components\s*,\s*codestream\.image_size\.uniform_bit_depth\s*,\s*"
                r"codestream\.image_size\.uniform_signed\s*,\s*offset"
            )
            selection_contract = {
                ("src/codestream/geometry.rs", "ImageSize::tile_count"): (
                    None, "part2_selection_tile_count", r"selection_geometry_view\s*\(\s*&\s*self\s*\)",
                ),
                ("src/codestream/geometry.rs", "ImageSize::tile_bounds"): (
                    None, "part2_selection_tile_bounds", r"selection_geometry_view\s*\(\s*self\s*\)\s*,\s*tile_index",
                ),
                ("src/options.rs", "selection_from_parts"): (
                    "decode_selection_value_view", "part2_selection_from_parts",
                    r"tile_selection_view\s*\(\s*&\s*tiles\s*\)\s*,\s*region\s*,\s*discard_levels",
                ),
                ("src/decode/arithmetic.rs", "ceil_div_u32"): (None, "part2_selection_ceil", r"value\s*,\s*divisor"),
                ("src/decode/selection.rs", "tile_list_contains"): (None, "part2_tile_list_contains", r"tiles@\s*,\s*tile"),
                ("src/decode/selection.rs", "selection_rectangle_area"): (None, "part2_rectangle_area", r"bounds"),
                ("src/decode/selection.rs", "validate_explicit_tile_indices"): (
                    None, "part2_explicit_tile_prefix", r"explicit_tiles@\s*,\s*tile_count\s*,\s*explicit_tiles@\.len\s*\(\s*\)",
                ),
                ("src/decode/selection.rs", "validate_selection_tile_rectangle"): (
                    None, "part2_validate_tile_rectangle", r"explicit_tiles@\s*,\s*tiles_across",
                ),
                ("src/decode/selection.rs", "validate_selection_rectangle_cells"): (
                    None, "part2_rectangle_rows",
                    r"explicit_tiles@\s*,\s*tiles_across\s*,\s*bounds\s*,\s*"
                    r"\(\s*bounds\.2\s+as\s+nat\s*-\s*bounds\.0\s+as\s+nat\s*\+\s*1\s*\)\s+as\s+nat",
                ),
                ("src/decode/selection.rs", "selection_region"): (
                    "selection_region_outcome", "part2_selection_region",
                    selection_geometry + r"\s*,\s*explicit_tiles@\s*,\s*requested\s*,\s*image_x1\s*,\s*image_y1",
                ),
                ("src/decode/selection.rs", "select_intersecting_tiles"): (
                    "selected_tiles_outcome", "part2_select_intersecting_tiles",
                    selection_geometry + r"\s*,\s*explicit_tiles@\s*,\s*region@\s*,\s*tile_count",
                ),
                ("src/decode/selection.rs", "explicit_tiles_from_selection"): (
                    "selected_tiles_outcome", "part2_selection_explicit",
                    r"crate::options::tile_selection_view\s*\(\s*selection\s*\)",
                ),
                ("src/decode/selection.rs", "validate_selection"): (
                    "validated_selection_outcome", "part2_validate_selection",
                    selection_geometry + r"\s*,\s*" + selection_view,
                ),
                ("src/decode/output.rs", "color_selection_from_validated"): (
                    "color_selection_outcome", "part2_color_selection_context",
                    r"size\.x_origin\s*,\s*size\.y_origin\s*,\s*crate::codestream::image_size_component_infos\s*\(\s*size\s*\)"
                    r"\s*,\s*size\.components\s*,\s*validated_selection_view\s*\(\s*validated\s*\)",
                ),
                ("src/decode/output.rs", "component_context_padding"): (
                    None, "part2_color_context_padding", r"target\s*,\s*sampling\s*,\s*registration",
                ),
                ("src/decode/output.rs", "color_selection_for_size"): (
                    "color_selection_outcome", "part2_color_selection_requested",
                    selection_geometry + r"\s*,\s*crate::codestream::image_size_component_infos\s*\(\s*size\s*\)"
                    r"\s*,\s*size\.components\s*,\s*crate::options::decode_selection_view\s*\(\s*requested\s*\)",
                ),
                ("src/decode/output.rs", "apply_associated_output"): (
                    "associated_typed_outcome", "part2_apply_associated_output",
                    r"crate::image::typed_image_value_view\s*\(\s*decoded\s*\)\s*,\s*" + selection_header
                    + r"\s*,\s*crate::limits::resource_component_limit\s*\(\s*limits\s*\)\s*,\s*" + selection_decoded_cap,
                ),
                ("src/decode/output.rs", "convert_associated_color"): (
                    "crate::color::converted_image_result", "part2_convert_associated",
                    selection_image + r"\s*,\s*" + selection_header + r"\s*,\s*" + selection_decoded_cap + r"\s*,\s*" + selection_work_cap,
                ),
                ("src/decode/output.rs", "convert_associated_selected_color"): (
                    "crate::color::converted_image_result", "part2_convert_associated_selected",
                    selection_image + r"\s*,\s*" + selection_header + r"\s*,\s*target\s*,\s*" + selection_decoded_cap + r"\s*,\s*" + selection_work_cap,
                ),
                ("src/decode/output.rs", "finish_associated_selected_output"): (
                    "crate::color::converted_image_result", "part2_finish_associated_selected_output",
                    r"crate::image::typed_image_value_view\s*\(\s*decoded\s*\)\s*,\s*" + selection_header + r"\s*,\s*target\s*,\s*"
                    r"crate::limits::resource_component_limit\s*\(\s*limits\s*\)\s*,\s*" + selection_decoded_cap + r"\s*,\s*" + selection_work_cap,
                ),
                ("src/jp2/container.rs", "associated_header_for_codestream"): (
                    "associated_header_outcome", "part2_associated_codestream_header",
                    r"codestream_header_association_view\s*\(\s*selected\s*\)\s*,\s*associated_header_view\s*\(\s*fallback\s*\)",
                ),
                ("src/jp2/container.rs", "validate_container_codestream"): (None, "part2_validate_selected_header", selected_header_arguments),
                ("src/jp2/container.rs", "validate_selected_header"): (None, "part2_validate_selected_header", selected_header_arguments),
            }.get((reference["path"], reference["symbol"]))
            if selection_contract:
                result_projection, expected_result_model = selection_contract[:2]
            header_contract = (
                _PACKET_HEADER_CONTRACTS.get((reference["path"], reference["symbol"]))
                or (_RAW_RECOVERY_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_RECOVERY_ENTRY else None)
                or (_RECONSTRUCTED_RECOVERY_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RECONSTRUCTED_RECOVERY_ENTRY else None)
                or _PACKET_PROGRESSION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _PACKET_WRAPPER_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _RECONSTRUCTION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TILE_COMPONENT_GEOMETRY_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _RESOLUTION_STYLE_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _RESOLUTION_GEOMETRY_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _PACKET_GRID_PRODUCER_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _SUBBAND_ADMISSION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _SUBBAND_VECTOR_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _DECODER_INITIALIZATION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _CODEBLOCK_PLANNING_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _PRECINCT_INITIALIZATION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _COMPONENT_PLAN_METADATA_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _CODEBLOCK_VECTOR_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _SUBBAND_EXECUTION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _PRECINCT_PLANNING_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _RESOLUTION_PLANNING_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _COMPONENT_TILE_PLANNING_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _PACKET_RECONSTRUCTION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _LAYOUT_ACCOUNTING_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TILE_METADATA_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _PROFILE_POLICY_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _PROFILE_RESULT_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _MAIN_HEADER_INITIALIZER_CONTRACTS.get((reference["path"], reference["symbol"]))
                or (_RAW_LAYOUT_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_LAYOUT_ENTRY else None)
                or _RAW_TILE_DECODING_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TILE_COLLECTION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _LAYOUT_DECODING_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _OUTPUT_SHAPE_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _NONLINEAR_REGIONS_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _NONLINEAR_ARITHMETIC_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _NONLINEAR_LUT_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _NONLINEAR_LOG_EXP_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _NONLINEAR_SCALAR_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _NONLINEAR_APPLICATION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TYPED_LAYOUT_CONTRACTS.get((reference["path"], reference["symbol"]))
                or (_RAW_TYPED_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_TYPED_ENTRY else None)
                or (_RAW_RECONSTRUCTED_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_RECONSTRUCTED_ENTRY else None)
                or (_JPX_SOURCE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPX_SOURCE_ENTRY else None)
                or (_JPX_LAYER_COLOR_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPX_LAYER_COLOR_ENTRY else None)
                or (_SOURCE_OPACITY_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _SOURCE_OPACITY_ENTRY else None)
                or (_COMPONENT_PLANE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _COMPONENT_PLANE_ENTRY else None)
                or (_GENERAL_LAYER_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _GENERAL_LAYER_ENTRY else None)
                or (_EFFECTIVE_LAYER_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _EFFECTIVE_LAYER_ENTRY else None)
                or (_SOURCE_FRAME_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _SOURCE_FRAME_ENTRY else None)
                or (_RAW_RENDER_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_RENDER_ENTRY else None)
                or (_RAW_COMPOSITION_RENDER_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_COMPOSITION_RENDER_ENTRY else None)
                or (_RAW_CONTAINER_IMAGE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_CONTAINER_IMAGE_ENTRY else None)
                or (_RAW_CONTAINER_COLOR_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_CONTAINER_COLOR_ENTRY else None)
                or (_RAW_JPX_PUBLIC_IMAGE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_JPX_PUBLIC_IMAGE_ENTRY else None)
                or (_JPIP_MESSAGE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPIP_MESSAGE_ENTRY else None)
                or (_JPIP_FRAGMENT_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPIP_FRAGMENT_ENTRY else None)
                or (_JPIP_CACHE_VIEW_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPIP_CACHE_VIEW_ENTRY else None)
                or (_JPIP_CACHE_INSERT_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPIP_CACHE_INSERT_ENTRY else None)
                or (_JPIP_LAYOUT_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPIP_LAYOUT_ENTRY else None)
                or (_JPIP_PLACEHOLDER_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPIP_PLACEHOLDER_ENTRY else None)
                or (_JPIP_RESPONSE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPIP_RESPONSE_ENTRY else None)
                or (_JPIP_RANGE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPIP_RANGE_ENTRY else None)
                or (_JPIP_PLANNED_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPIP_PLANNED_ENTRY else None)
                or (_JPIP_TRANSCODE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPIP_TRANSCODE_ENTRY else None)
                or (_JPIP_PROGRESSIVE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPIP_PROGRESSIVE_ENTRY else None)
                or (_JPIP_TRANSITION_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPIP_TRANSITION_ENTRY else None)
                or (_JPIP_PHASE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPIP_PHASE_ENTRY else None)
                or (_JPIP_BYTE_RESULT_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPIP_BYTE_RESULT_ENTRY else None)
                or ((_JPIP_AUTOMATIC_INPUT_CONTRACTS.get((reference["path"], reference["symbol"]))
                     or _JPIP_TRANSITION_CONTRACTS.get((reference["path"], reference["symbol"]))
                     or _JPIP_CACHE_VIEW_CONTRACTS.get((reference["path"], reference["symbol"])))
                    if entry["id"] == _JPIP_AUTOMATIC_INPUT_ENTRY else None)
                or (_JPX_INSPECTION_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _JPX_INSPECTION_ENTRY else None)
                or (_RAW_JPX_INSPECTION_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_JPX_INSPECTION_ENTRY else None)
                or (_BOX_READER_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _BOX_READER_ENTRY else None)
                or (_FILE_TYPE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _FILE_TYPE_ENTRY else None)
                or (_IMAGE_HEADER_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _IMAGE_HEADER_ENTRY else None)
                or (_COLOR_HEADER_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _COLOR_HEADER_ENTRY else None)
                or (_CHANNEL_HEADER_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _CHANNEL_HEADER_ENTRY else None)
                or (_RESOLUTION_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RESOLUTION_ENTRY else None)
                or (_PALETTE_VALUE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _PALETTE_VALUE_ENTRY else None)
                or (_PALETTE_RESULT_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _PALETTE_RESULT_ENTRY else None)
                or (_RAW_JP2_HEADER_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_JP2_HEADER_ENTRY else None)
                or (_OWNED_HEADER_CLONE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _OWNED_HEADER_CLONE_ENTRY else None)
                or (_ASSOCIATION_CLONE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _ASSOCIATION_CLONE_ENTRY else None)
                or (_RAW_CONTAINER_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_CONTAINER_ENTRY else None)
                or (_RAW_INSPECTED_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_INSPECTED_ENTRY else None)
                or (_ASSOCIATED_HEADER_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _ASSOCIATED_HEADER_ENTRY else None)
                or (_METADATA_TREE_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _METADATA_TREE_ENTRY else None)
                or (_RAW_LAYER_HEADER_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_LAYER_HEADER_ENTRY else None)
                or (_RAW_COMPOSITION_CONTRACTS.get((reference["path"], reference["symbol"]))
                    if entry["id"] == _RAW_COMPOSITION_ENTRY else None)
                or _CODESTREAM_READER_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _SOT_READER_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TILE_DATA_WINDOW_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _SIZ_GEOMETRY_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _LAYOUT_PROLOGUE_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TILE_LOOP_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _MAIN_HEADER_ADMISSION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TILE_HEADER_ADMISSION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _RAW_TILE_HEADER_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _ROI_SETTER_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TILE_PART_READER_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _PERSISTENT_TILE_CONFIGURATION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _INHERITED_TILE_CONFIGURATION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _MCT_PARAMETER_CLONE_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _OWNED_TILE_INHERITANCE_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _CODING_STYLE_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _COMPONENT_STYLE_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _QUANTIZATION_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _COMPONENT_MARKER_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _DECOMPOSITION_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _DECOMPOSITION_RESOLUTION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _MAIN_COMPONENT_FINALIZATION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _STYLE_OVERRIDE_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _QUANTIZATION_OVERRIDE_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TILE_COMPONENT_FINALIZATION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _COMPONENT_SEGMENT_ADMISSION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _COMPONENT_DEPTH_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _COMPONENT_HEADER_APPLICATION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _PROFILE_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _NONLINEAR_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TILE_LENGTH_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _KERNEL_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _PROGRESSION_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _PROGRESSION_ADMISSION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TRANSFORM_ROUTING_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TRANSFORM_COLLECTION_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _COLLECTION_FRAGMENT_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TRANSFORM_FRAGMENT_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TRANSFORM_REGISTRY_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TRANSFORM_GRAPH_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _PACKED_HEADER_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _PACKET_LENGTH_ADMISSION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TILE_PACKET_ADMISSION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _PACKET_METADATA_FINALIZATION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TRANSFORM_ARRAY_BYTES_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _DECODER_ADMISSION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _DECODER_LAYOUT_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _LAYER_STATE_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _LAYER_REGISTRATION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _LAYER_SAMPLING_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _LAYER_TRAVERSAL_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _LAYER_KEY_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _LAYER_COMPONENT_KEY_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _LAYER_OPACITY_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _LAYER_EXTERNAL_ALPHA_CONTRACTS.get((reference["path"], reference["symbol"]))
            )
            if header_contract:
                expected_result_model = header_contract[0]
            if (reference["path"], reference["symbol"]) in _TILE_DATA_WINDOW_CONTRACTS and {
                "path": "specs/packet_input.rs", "symbol": "part1_tile_data_window",
            } not in entry["spec_refs"]:
                raise ValueError("tile-data window model must be bound to specs/packet_input.rs")
            if (reference["path"], reference["symbol"]) in (
                ("src/tier1/coding.rs", "Tier1CodingStyle::set_force_high_throughput"),
                ("src/tier1/contributions.rs", "Tier1CodeBlockDecoder::set_multiple_ht_sets_allowed"),
                ("src/codestream/mct_resolution.rs", "replace_mct_array"),
                ("src/codestream/mct_resolution.rs", "replace_mct_record"),
            ) and re.search(r"\)\s*->", text[signature:body_start]):
                raise ValueError(f"linked unit-state contract requires the actual implicit unit return: {short}")
            projected_result = re.search(
                named_prefix + re.escape(result_projection) + r"\(\s*\1\s*\)" + model_suffix,
                contract,
            ) if result_projection else None
            if header_contract:
                projected_result = re.search(named_prefix + header_contract[1] + model_suffix, contract)
            main_header_contract = (reference["path"], reference["symbol"]) == _MAIN_HEADER_LAYOUT
            if main_header_contract and entry["id"] == _RAW_LAYOUT_ENTRY:
                projected_result = re.search(
                    named_prefix + _coverage_call(
                        "crate::specs::part1_main_header_layout_relation",
                        _coverage_call("crate::specs::part1_read_main_header", _coverage_call("parser_view", r"&\s*self")),
                        _coverage_call("layout_main_header_outcome", r"\1"),
                    ) + r"\s*,\s*" + header_contract[1] + model_suffix, contract,
                )
            elif main_header_contract:
                expected_result_model = "part1_main_header_layout_relation"
                projected_result = re.search(
                    named_prefix + r"crate::specs::(?P<model>part1_main_header_layout_relation)\s*\(\s*"
                    + _coverage_call("crate::specs::part1_read_main_header",
                                     _coverage_call("parser_view", r"&\s*self"))
                    + r"\s*,\s*" + _coverage_call("layout_main_header_outcome", r"\1") + r"\s*\)",
                    contract,
                ) if re.search(r"\brequires\b", contract) is None else None
            state_term = (
                r"(?:final\(\s*\w+\s*\)@|"
                r"crate::specs::part2_composition_planes\(\s*final\(\s*\w+\s*\)@\s*\)|"
                r"\*\s*final\(\s*\w+\s*\)(?:\s+as\s+nat)?)"
            )
            reader_contracts = {
                "HtRefinementPlaneState::magnitude_sample": ("ht_refinement_core_view", "ht_magref_sample"),
                "HtRefinementPlaneState::magnitude_column": ("ht_refinement_core_view", "ht_magref_rows"),
                "HtRefinementPlaneState::magnitude_stripe": ("ht_refinement_core_view", "ht_magref_columns"),
                "HtRefinementPlaneState::magnitude_pass": ("ht_refinement_core_view", "ht_magref_stripes"),
                "HtSignificancePatchState::discover_sample": ("ht_sigprop_patch_view", "ht_discover_sample"),
                "HtSignificancePatchState::discover_column": ("ht_sigprop_patch_view", "ht_discovery_rows"),
                "HtSignificancePatchState::discover_patch": ("ht_sigprop_patch_view", "ht_discovery_columns"),
                "HtSignificancePatchState::sign_sample": ("ht_sigprop_patch_view", "ht_patch_sign_sample"),
                "HtSignificancePatchState::signs": ("ht_sigprop_patch_view", "ht_pending_signs"),
                "CodeBlockPlane::apply_ht_refinement_decision": ("code_block_plane_view", "ht_apply_refinement"),
                "Tier1CodeBlockDecoder::decode_high_throughput_segments": ("tier1_decoder_state", "ht_decode_segments"),
                "Tier1CodeBlockDecoder::decode_ht_coefficient_symbols": ("tier1_decoder_state", "ht_coefficient_symbols"),
                "Tier1CodeBlockDecoder::decode_high_throughput_refinement": ("tier1_decoder_state", "ht_decode_refinement_contribution"),
                "Tier1CodeBlockDecoder::skip_high_throughput_segment": ("tier1_decoder_state", "ht_skip_segment"),
                "Tier1CodeBlockDecoder::run_ht_placeholder_groups": ("tier1_decoder_state", "ht_placeholder_group_run"),
                "Tier1CodeBlockDecoder::decode_ht_staged_group": ("tier1_decoder_state", "ht_decode_staged_group"),
                "Tier1CodeBlockDecoder::store_ht_coefficient_symbols": (
                    "tier1_decoder_state", "ht_store_coefficient_symbols",
                ),
                "HtCleanupPlaneReconstruction::sample": ("ht_plane_view", "ht_plane_sample"),
                "HtCleanupPlaneReconstruction::quad": ("ht_plane_view", "ht_plane_quad"),
                "HtCleanupPlaneReconstruction::finish": ("ht_plane_view", "ht_plane_finish"),
                "CodeBlockPlane::mark_significant_magnitude": ("code_block_plane_view", "tier1_mark_coefficient"),
                "CoefficientState::set_magnitude": ("coefficient_state_view", "tier1_set_magnitude"),
                "RawBitReader::read_bit": ("raw_bit_reader_view", "part1_raw_reader_read"),
                "RawBitReader::load_byte": ("raw_bit_reader_view", "part1_raw_reader_load"),
                "HtMelBitReader::load_byte": ("ht_mel_view", "ht_mel_load"),
                "HtMelBitReader::read_bit": ("ht_mel_view", "ht_mel_read"),
                "HtReverseVlcReader::load_previous_byte": ("ht_reverse_vlc_view", "ht_reverse_vlc_load"),
                "HtReverseVlcReader::read_bit": ("ht_reverse_vlc_view", "ht_reverse_vlc_read"),
                "HtCleanupReaders::tick": ("ht_cleanup_readers_view", "ht_cleanup_reader_tick"),
                "HtCleanupReaders::read_mel_bit": ("ht_cleanup_readers_view", "ht_cleanup_reader_read_mel"),
                "HtCleanupReaders::read_vlc_bit": ("ht_cleanup_readers_view", "ht_cleanup_reader_read_vlc"),
                "HtForwardMagSgnReader::load_byte": ("ht_magsgn_view", "ht_magsgn_load"),
                "HtForwardMagSgnReader::read_bit": ("ht_magsgn_view", "ht_magsgn_read"),
                "HtForwardMagSgnReader::read_bits": ("ht_magsgn_view", "ht_magsgn_read_bits"),
                "HtForwardMagSgnReader::finish": ("ht_magsgn_view", "ht_magsgn_finish"),
                "HtForwardRefinementReader::load_byte": ("ht_forward_refinement_view", "ht_forward_refinement_load"),
                "HtForwardRefinementReader::read_positioned_bit": ("ht_forward_refinement_view", "ht_forward_refinement_positioned"),
                "HtForwardRefinementReader::read_bit": ("ht_forward_refinement_view", "ht_forward_refinement_read"),
                "HtReverseRefinementReader::load_previous_byte": ("ht_reverse_refinement_view", "ht_reverse_refinement_load"),
                "HtReverseRefinementReader::read_positioned_bit": ("ht_reverse_refinement_view", "ht_reverse_refinement_positioned"),
                "HtReverseRefinementReader::read_bit": ("ht_reverse_refinement_view", "ht_reverse_refinement_read"),
                "HtRefinementReaders::claim": ("ht_refinement_readers_view", "ht_refinement_claim"),
                "HtRefinementReaders::read_forward": ("ht_refinement_readers_view", "ht_refinement_read_forward"),
                "HtRefinementReaders::read_reverse": ("ht_refinement_readers_view", "ht_refinement_read_reverse"),
                "HtCleanupReaders::advance_vlc": ("ht_cleanup_readers_view", "ht_cleanup_advance_vlc"),
                "HtCleanupReaders::mel_event": ("ht_cleanup_readers_view", "ht_cleanup_mel_event"),
                "HtCleanupReaders::read_prefix": ("ht_cleanup_readers_view", "ht_uvlc_prefix"),
                "HtCleanupReaders::read_suffix": ("ht_cleanup_readers_view", "ht_uvlc_suffix"),
                "HtCleanupReaders::prefix_value": ("ht_cleanup_readers_view", "ht_uvlc_prefix_value"),
                "HtCleanupReaders::decode_initial_u": ("ht_cleanup_readers_view", "ht_uvlc_initial"),
                "HtCleanupReaders::decode_non_initial_u": ("ht_cleanup_readers_view", "ht_uvlc_non_initial"),
                "HtCleanupReaders::decode_quad_word": ("ht_cleanup_readers_view", "ht_cleanup_quad_word"),
            }
            reader_contract = reader_contracts.get(reference["symbol"]) if (
                reference["path"] == "src/tier1.rs" or reference["path"].startswith("src/tier1/")
            ) else None
            if reader_contract:
                state_term = (
                    r"(?:" + state_term
                    + "|" + re.escape(reader_contract[0]) + r"\(\s*final\(\s*self\s*\)\s*\))"
                )
            state_tail = r"\s*,\s*" + state_term + r"(?:\s*,\s*" + state_term + r")*\s*\))"
            state_result = re.search(
                named_prefix + r"(?P<state>\(\s*\1" + state_tail + model_suffix, contract,
            )
            if state_result is None:
                state_result = re.search(
                    named_prefix + r"\1\.is_ok\(\)\s*==>\s*"
                    + r"(?P<state>\(\s*\1\.is_ok\(\)" + state_tail + model_suffix, contract,
                )
            if (reference["path"], short) == ("src/tier1/ht_cleanup.rs", "reconstruct_ht_magnitude"):
                state_result = re.search(
                    named_prefix
                    + r"(?P<state>\(\s*ht_numeric_magnitude_outcome\(\s*\1\s*\)\s*,\s*"
                    r"ht_magsgn_view\(\s*final\(\s*reader\s*\)\s*\)\s*\))"
                    + model_suffix
                    + r"\s*ht_magsgn_view\(\s*old\(\s*reader\s*\)\s*\)\s*,\s*"
                    r"completed_u\s*,\s*embedded_bit\s*,\s*embedded_value\s*,\s*decoded_bitplanes\s*,?\s*\)",
                    contract,
                )
            if packet_contract and packet_contract[1] is not None:
                state_result = re.search(
                    named_prefix + r"(?P<state>\(\s*\1\s*,\s*" + packet_contract[1] + r"\s*\))" + model_suffix,
                    contract,
                )
            if header_contract and header_contract[2] is not None:
                state_result = re.search(
                    named_prefix + r"(?P<state>\(\s*" + header_contract[1] + r"\s*,\s*"
                    + header_contract[2] + r"\s*\))" + model_suffix, contract,
                )
            storage_contract = {
                "reserve_additional": (
                    "storage_reservation_result",
                    r"old\(\s*values\s*\)@\s*,\s*final\(\s*values\s*\)@\s*,\s*\1",
                ),
                "empty_with_capacity": ("storage_capacity_result", r"\1"),
                "extend_bytes": (
                    "storage_extension_result",
                    r"old\(\s*values\s*\)@\s*,\s*bytes@\s*,\s*"
                    r"final\(\s*values\s*\)@\s*,\s*\1",
                ),
            }.get(short) if reference["path"] == "src/allocation.rs" else None
            if (reference["path"], reference["symbol"]) == (
                    "src/jpip/automatic_headers.rs", "normalize_main_header"):
                storage_contract = (
                    "part2_jpip_main_header_result",
                    r"input@\s*,\s*jpip_packet_bytes_outcome\(\s*\1\s*\)",
                )
            if (reference["path"], reference["symbol"]) == (
                    "src/jpip/progression.rs", "DatabinCache::automatic_headers"):
                storage_contract = (
                    "part2_jpip_automatic_headers_result",
                    r"jpip_cache_view\(\s*self\s*\)\s*,\s*codestream\s*,\s*"
                    r"jpip_automatic_headers_outcome\(\s*\1\s*\)",
                )
            if storage_contract:
                model, arguments = storage_contract
                relation = re.search(
                    named_prefix + r"crate::specs::(?P<model>" + re.escape(model)
                    + r")\s*\(\s*(?P<state>" + arguments + r")\s*,?\s*\)", contract,
                )
                if relation is None or re.search(r"\brequires\b", contract):
                    raise ValueError(f"linked function lacks executable Verus contract: {short}; invalid storage relation")
                if mutating:
                    state_result = relation
                else:
                    scalar_result = relation
                expected_result_model = model
            recovery_relations = (
                _RAW_RECOVERY_RELATIONS if entry["id"] == _RAW_RECOVERY_ENTRY
                else _RECONSTRUCTED_RECOVERY_RELATIONS if entry["id"] == _RECONSTRUCTED_RECOVERY_ENTRY
                else {}
            )
            recovery_relation = recovery_relations.get((reference["path"], reference["symbol"]))
            if recovery_relation:
                model, arguments = recovery_relation
                relation = re.search(
                    named_prefix + r"crate::specs::(?P<model>" + re.escape(model)
                    + r")\s*\(\s*(?P<state>" + arguments + r")\s*,?\s*\)", contract,
                )
                if relation is None or re.search(r"\brequires\b", contract):
                    raise ValueError(f"linked function lacks executable Verus contract: {short}; invalid recovery relation")
                scalar_result = relation
                expected_result_model = model
            final_parameters = set(re.findall(
                r"\bfinal\(\s*(\w+(?:\.\w+)?)\s*\)" if bundle else r"\bfinal\(\s*(\w+)\s*\)",
                state_result["state"],
            )) if state_result is not None else set()
            complete_state = bool(mutable_parameters) and final_parameters == mutable_parameters
            named_result = state_result if mutating else scalar_result or projected_result or state_result
            expected_constructor = {
                "ht_mel_from_input": "ht_mel_initial",
                "ht_reverse_vlc_from_input": "ht_reverse_vlc_initial",
                "ht_cleanup_readers_from_inputs": "ht_cleanup_readers_initial",
                "ht_magsgn_from_input": "ht_magsgn_initial",
                "ht_forward_refinement_from_input": "ht_forward_refinement_initial",
                "ht_reverse_refinement_from_input": "ht_reverse_refinement_initial",
                "ht_refinement_readers_from_inputs": "ht_refinement_readers_initial",
            }.get(short) if (
                reference["path"] == "src/tier1.rs" or reference["path"].startswith("src/tier1/")
            ) else None
            if expected_constructor and (named_result is None or named_result["model"] != expected_constructor):
                raise ValueError(f"linked function lacks executable Verus contract: {short}; wrong constructor model")
            if (reference["path"], reference["symbol"]) == ("src/tier1/ht_cleanup_readers.rs", "HtCleanupReaders::can_claim_byte"):
                if named_result is None or named_result["model"] != "ht_cleanup_reader_can_claim":
                    raise ValueError(f"linked function lacks executable Verus contract: {short}; wrong claim model")
            if reader_contract:
                view, model = reader_contract
                complete_reader_state = (
                    state_result is not None
                    and state_result["model"] == model
                    and re.fullmatch(
                        r"\(\s*" + re.escape(state_result[1]) + r"\s*,\s*"
                        + re.escape(view) + r"\(\s*final\(\s*self\s*\)\s*\)\s*\)",
                        state_result["state"],
                    ) is not None
                    and re.search(
                        r"==\s*crate::specs::" + re.escape(model) + r"\(\s*"
                        + re.escape(view) + r"\(\s*old\(\s*self\s*\)\s*\)",
                        contract,
                    ) is not None
                )
                if not complete_reader_state:
                    raise ValueError(
                        f"linked function lacks executable Verus contract: {reference['symbol']}; "
                        "incomplete exact reader state relation"
                    )
            metadata_arguments_bound = (
                (reference["path"], short) != ("src/tier1/ht_metadata.rs", "decode_ht_cleanup_segment_metadata")
                or _coverage_result_arguments(
                    contract, named_result, "ht_cleanup_segment_metadata",
                    r"ht_cleanup_segment_view\s*\(\s*&\s*cleanup\s*\)\s*,\s*"
                    r"width\s*,\s*height\s*,\s*maximum_u\s*,\s*"
                    r"crate::limits::resource_work_limit\s*\(\s*limits\s*\)",
                )
            )
            palette_arguments_bound = (
                (reference["path"], reference["symbol"]) != ("src/jp2/color.rs", "Palette::value")
                or _coverage_result_arguments(
                    contract, named_result, "part2_palette_value",
                    r"palette_view\s*\(\s*self\s*\)\s*,\s*entry\s*,\s*column",
                )
            )
            cleanup_contract_arguments = {
                "prepare_ht_cleanup_symbols": (
                    "ht_cleanup_prepare",
                    r"code_block_plane_view\s*\(\s*plane\s*\)\s*,\s*"
                    r"ht_cleanup_segment_view\s*\(\s*&\s*cleanup\s*\)\s*,\s*"
                    r"maximum_passes\s*,\s*maximum_u\s*,\s*skipped_bitplanes\s*,\s*"
                    r"crate::limits::resource_work_limit\s*\(\s*limits\s*\)",
                ),
                "Tier1CodeBlockDecoder::store_ht_coefficient_symbols": (
                    "ht_store_coefficient_symbols",
                    r"tier1_decoder_state\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*"
                    r"code_block_plane_view\s*\(\s*&\s*output\s*\)\s*,\s*"
                    r"code_block_plane_view\s*\(\s*&\s*cleanup_plane\s*\)\s*,\s*"
                    r"statistics\s*,\s*decoded_bitplanes\s*,\s*pass_count\s*,\s*bytes\s*,\s*has_refinement",
                ),
                "CodeBlockPlane::duplicate": (
                    "tier1_duplicate_plane", r"code_block_plane_view\s*\(\s*self\s*\)",
                ),
            }.get(reference["symbol"]) if (
                reference["path"] == "src/tier1.rs" or reference["path"].startswith("src/tier1/")
            ) else None
            cleanup_arguments_bound = (
                cleanup_contract_arguments is None
                or _coverage_result_arguments(
                    contract, named_result, cleanup_contract_arguments[0], cleanup_contract_arguments[1],
                )
            )
            refinement_contract_arguments = {
                "decode_ht_refinement_plane": (
                    "ht_refinement_plane",
                    r"code_block_plane_view\s*\(\s*cleanup_plane\s*\)\s*,\s*"
                    r"ht_refinement_segment_view\s*\(\s*&\s*segment\s*\)\s*,\s*"
                    r"refinement_passes\s*,\s*decoded_bitplanes\s*,\s*vertical_causal_context\s*,\s*"
                    r"crate::limits::resource_work_limit\s*\(\s*limits\s*\)",
                ),
                "HtRefinementPlaneState::magnitude_sample": (
                    "ht_magref_sample",
                    r"ht_refinement_core_view\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*"
                    r"x\s*,\s*y\s*,\s*crate::magnitude::magnitude_value\s*\(\s*delta\s*\)\s*,\s*decoded_bitplanes",
                ),
                "HtRefinementPlaneState::magnitude_column": (
                    "ht_magref_rows",
                    r"ht_refinement_core_view\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*"
                    r"x\s*,\s*stripe_y\s*,\s*rows\s+as\s+nat\s*,\s*0\s*,\s*"
                    r"crate::magnitude::magnitude_value\s*\(\s*delta\s*\)\s*,\s*decoded_bitplanes",
                ),
                "HtRefinementPlaneState::magnitude_stripe": (
                    "ht_magref_columns",
                    r"ht_refinement_core_view\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*"
                    r"width\s*,\s*stripe_y\s*,\s*rows\s+as\s+nat\s*,\s*0\s*,\s*"
                    r"crate::magnitude::magnitude_value\s*\(\s*delta\s*\)\s*,\s*decoded_bitplanes",
                ),
                "HtRefinementPlaneState::magnitude_pass": (
                    "ht_magref_stripes",
                    r"ht_refinement_core_view\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*"
                    r"width\s*,\s*height\s*,\s*0\s*,\s*"
                    r"crate::magnitude::magnitude_value\s*\(\s*delta\s*\)\s*,\s*decoded_bitplanes",
                ),
                "HtSignificancePatchState::discover_sample": (
                    "ht_discover_sample",
                    r"ht_sigprop_patch_view\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*"
                    r"x\s*,\s*y\s*,\s*ht_refinement_magnitude_view\s*\(\s*magnitude\s*\)\s*,\s*vertical_causal_context",
                ),
                "HtSignificancePatchState::discover_column": (
                    "ht_discovery_rows",
                    r"ht_sigprop_patch_view\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*"
                    r"x\s*,\s*stripe_y\s*,\s*rows\s+as\s+nat\s*,\s*0\s*,\s*"
                    r"ht_refinement_magnitude_view\s*\(\s*magnitude\s*\)\s*,\s*causal",
                ),
                "HtSignificancePatchState::discover_patch": (
                    "ht_discovery_columns",
                    r"ht_sigprop_patch_view\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*"
                    r"end\s*,\s*stripe_y\s*,\s*rows\s+as\s+nat\s*,\s*start\s+as\s+nat\s*,\s*"
                    r"ht_refinement_magnitude_view\s*\(\s*magnitude\s*\)\s*,\s*causal",
                ),
                "HtSignificancePatchState::sign_sample": (
                    "ht_patch_sign_sample",
                    r"ht_sigprop_patch_view\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*"
                    r"index\s+as\s+nat\s*,\s*ht_refinement_magnitude_view\s*\(\s*magnitude\s*\)",
                ),
                "HtSignificancePatchState::signs": (
                    "ht_pending_signs",
                    r"ht_sigprop_patch_view\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*"
                    r"0\s*,\s*ht_refinement_magnitude_view\s*\(\s*magnitude\s*\)",
                ),
                "run_ht_significance_stripe": (
                    "ht_sigprop_patches",
                    r"ht_sigprop_plane_view\s*\(\s*&\s*input\s*\)\s*,\s*"
                    r"width\s*,\s*stripe_y\s*,\s*rows\s+as\s+nat\s*,\s*0\s*,\s*"
                    r"ht_refinement_magnitude_view\s*\(\s*magnitude\s*\)\s*,\s*causal",
                ),
                "run_ht_significance_pass": (
                    "ht_sigprop_stripes",
                    r"ht_sigprop_plane_view\s*\(\s*&\s*input\s*\)\s*,\s*"
                    r"width\s*,\s*height\s*,\s*0\s*,\s*"
                    r"ht_refinement_magnitude_view\s*\(\s*magnitude\s*\)\s*,\s*causal",
                ),
                "ht_significance_magnitude": ("ht_significance_magnitude", r"decoded_bitplanes"),
                "ht_refinement_delta": ("ht_refinement_delta", r"decoded_bitplanes"),
                "ht_collect_cleanup_significance": (
                    "ht_cleanup_significance", r"coefficient_raw_views\s*\(\s*coefficients@\s*\)",
                ),
                "CodeBlockPlane::apply_ht_refinement_decision": (
                    "ht_apply_refinement",
                    r"code_block_plane_view\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*"
                    r"x\s*,\s*y\s*,\s*crate::magnitude::magnitude_value\s*\(\s*delta\s*\)\s*,\s*refinement_bit",
                ),
                "CodeBlockPlane::neighbor_summary_with_causality": (
                    "ht_neighbors",
                    r"code_block_plane_view\s*\(\s*self\s*\)\s*,\s*x\s*,\s*y\s*,\s*vertical_causal_context",
                ),
                "CodeBlockPlane::accumulate_neighbor": (
                    "ht_accumulate_neighbor",
                    r"code_block_plane_view\s*\(\s*self\s*\)\s*,\s*x\s*,\s*y\s*,\s*"
                    r"delta\.0\s*,\s*delta\.1\s*,\s*neighbor_kind_tag\s*\(\s*kind\s*\)\s*,\s*"
                    r"\*\s*old\s*\(\s*summary\s*\)",
                ),
                "ht_neighbor_summary_zero": ("ht_neighbor_zero", r""),
                "significant_neighbor_count": ("ht_significant_neighbor_count", r"summary"),
                "Tier1CodeBlockDecoder::decode_high_throughput_segments": (
                    "ht_decode_segments",
                    r"tier1_decoder_state\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*"
                    r"cleanup@\s*,\s*cleanup_passes\s*,\s*ht_optional_bytes_view\s*\(\s*refinement\s*\)\s*,\s*"
                    r"refinement_passes\s*,\s*crate::limits::resource_code_block_pass_limit\s*\(\s*limits\s*\)\s*,\s*"
                    r"crate::limits::resource_code_block_byte_limit\s*\(\s*limits\s*\)\s*,\s*"
                    r"crate::limits::resource_work_limit\s*\(\s*limits\s*\)",
                ),
                "Tier1CodeBlockDecoder::decode_ht_coefficient_symbols": (
                    "ht_coefficient_symbols",
                    r"tier1_decoder_state\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*"
                    r"ht_block_segments_view\s*\(\s*&\s*segments\s*\)\s*,\s*"
                    r"pass_count\s*,\s*maximum_u\s*,\s*skipped_bitplanes\s*,\s*"
                    r"crate::limits::resource_work_limit\s*\(\s*limits\s*\)",
                ),
                "Tier1CodeBlockDecoder::decode_high_throughput_refinement": (
                    "ht_decode_refinement_contribution",
                    r"tier1_decoder_state\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*input@\s*,\s*passes\s*,\s*"
                    r"crate::limits::resource_code_block_byte_limit\s*\(\s*limits\s*\)\s*,\s*"
                    r"crate::limits::resource_work_limit\s*\(\s*limits\s*\)",
                ),
                "Tier1CodeBlockDecoder::skip_high_throughput_segment": (
                    "ht_skip_segment",
                    r"tier1_decoder_state\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*passes\s*,\s*"
                    r"crate::limits::resource_code_block_pass_limit\s*\(\s*limits\s*\)",
                ),
                "Tier1CodeBlockDecoder::run_ht_placeholder_groups": (
                    "ht_placeholder_group_run",
                    r"tier1_decoder_state\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*placeholder_passes\s+as\s+nat\s*,\s*"
                    r"crate::limits::resource_code_block_pass_limit\s*\(\s*limits\s*\)",
                ),
                "Tier1CodeBlockDecoder::decode_ht_staged_group": (
                    "ht_decode_staged_group",
                    r"tier1_decoder_state\s*\(\s*old\s*\(\s*self\s*\)\s*\)\s*,\s*input@\s*,\s*passes\s*,\s*"
                    r"crate::limits::resource_code_block_pass_limit\s*\(\s*limits\s*\)\s*,\s*"
                    r"crate::limits::resource_code_block_byte_limit\s*\(\s*limits\s*\)\s*,\s*"
                    r"crate::limits::resource_work_limit\s*\(\s*limits\s*\)",
                ),
                "ht_significant_bitplanes": ("ht_significant_bitplanes", r"maximum_passes"),
                "Tier1BlockCoding::uses_high_throughput": ("ht_block_coding_enabled", r"self"),
                "copy_ht_refinement_bytes": ("ht_copy_refinement_bytes", r"input@"),
                "Tier1PassStatistics::merge": (
                    "tier1_statistics_merge", r"\*\s*old\s*\(\s*self\s*\)\s*,\s*other",
                ),
            }.get(reference["symbol"]) if (
                reference["path"] == "src/tier1.rs" or reference["path"].startswith("src/tier1/")
            ) else None
            refinement_arguments_bound = (
                refinement_contract_arguments is None
                or _coverage_result_arguments(
                    contract, named_result, refinement_contract_arguments[0], refinement_contract_arguments[1],
                )
            )
            prepare_contract_arguments = {
                "prepare_tile_component": (
                    "part1_prepare_standard_component",
                    r"prepare_plan_view\s*\(\s*plan\s*\)\s*,\s*"
                    r"prepare_precincts_view\s*\(\s*precincts@\s*\)\s*,\s*"
                    r"prepare_style_view\s*\(\s*coding_style\s*\)\s*,\s*"
                    r"crate::limits::resource_decoded_bytes_limit\s*\(\s*limits\s*\)",
                ),
                "initialize_prepare_working": (
                    "part1_prepare_init_prefix",
                    r"bands@\s*,\s*fraction\s*,\s*"
                    r"crate::limits::resource_decoded_bytes_limit\s*\(\s*limits\s*\)\s*,\s*"
                    r"selected\s+as\s+nat",
                ),
                "collect_prepare_coefficients": (
                    "part1_prepare_collect_coefficients",
                    r"crate::tier1::code_block_plane_view\s*\(\s*plane\s*\)",
                ),
                "collect_prepare_cell": (
                    "part1_prepare_signed_cell",
                    r"crate::tier1::code_block_plane_view\s*\(\s*plane\s*\)\s*,\s*x\s*,\s*y",
                ),
                "copy_prepare_plane": (
                    "part1_prepare_copy_plane",
                    r"crate::transform::reconstructed_plane_view\s*\(\s*plane\s*\)\s*,\s*first_detail",
                ),
                "finish_prepared_component": (
                    "part1_prepare_finish",
                    r"prepare_plan_view\s*\(\s*plan\s*\)\s*,\s*fraction\s*,\s*folded@",
                ),
                "PreparedTileComponent::as_tile_component": (
                    "part1_prepared_as_tile", r"prepared_component_view\s*\(\s*\*\s*self\s*\)",
                ),
            }.get(reference["symbol"]) if reference["path"] == "src/decode/reconstruction.rs" else None
            prepare_arguments_bound = (
                prepare_contract_arguments is None
                or _coverage_result_arguments(
                    contract, named_result, prepare_contract_arguments[0], prepare_contract_arguments[1],
                )
            )
            component_contract_arguments = {
                ("src/decode/output.rs", "copy_typed_component"): (
                    "part2_typed_component_copy",
                    r"crate::image::typed_component_output_view\s*\(\s*source\s*\)",
                ),
                ("src/decode/output.rs", "map_palette_component"): (
                    "part2_palette_component",
                    r"crate::image::typed_component_view\s*\(\s*source\s*\)\s*,\s*"
                    r"crate::jp2::palette_view\s*\(\s*palette\s*\)\s*,\s*column",
                ),
                ("src/decode/output.rs", "palette_modulus"): ("part2_palette_modulus", r"precision"),
                ("src/decode/output.rs", "invalid_jp2_output"): ("part2_color_input_error", r""),
                ("src/image/layout.rs", "typed_component_from_parts"): (
                    "part2_typed_component_from_parts",
                    r"width\s*,\s*height\s*,\s*info\s*,\s*typed_samples_view\s*\(\s*&\s*samples\s*\)",
                ),
                ("src/decode/output.rs", "apply_jp2_output"): (
                    "part2_apply_output_header",
                    r"crate::image::typed_image_value_view\s*\(\s*decoded\s*\)\s*,\s*"
                    r"jp2::output_header_view\s*\(\s*header\s*\)\s*,\s*"
                    r"crate::limits::resource_component_limit\s*\(\s*limits\s*\)\s*,\s*"
                    r"crate::limits::resource_decoded_bytes_limit\s*\(\s*limits\s*\)",
                ),
                ("src/image/layout.rs", "typed_image_from_components_with_origin"): (
                    "part2_typed_image_from_parts",
                    r"width\s*,\s*height\s*,\s*x_origin\s*,\s*y_origin\s*,\s*"
                    r"typed_components_output_view\s*\(\s*components\s*@\s*\)\s*,\s*"
                    r"crate::limits::resource_component_limit\s*\(\s*limits\s*\)\s*,\s*"
                    r"crate::limits::resource_decoded_bytes_limit\s*\(\s*limits\s*\)",
                ),
                ("src/image/layout.rs", "TypedImage::component"): (
                    "part2_typed_image_component",
                    r"typed_components_output_view\s*\(\s*typed_image_components\s*\(\s*self\s*\)\s*\)\s*,\s*index",
                ),
            }.get((reference["path"], reference["symbol"]))
            component_arguments_bound = (
                component_contract_arguments is None
                or _coverage_result_arguments(
                    contract, named_result, component_contract_arguments[0], component_contract_arguments[1],
                )
            )
            arbitrary_arguments_bound = (
                arbitrary_contract is None
                or _coverage_result_arguments(contract, named_result, arbitrary_contract[1], arbitrary_contract[2])
            )
            packet_arguments_bound = (
                packet_contract is None
                or _coverage_result_arguments(contract, named_result, packet_contract[0], packet_contract[2])
            )
            selection_arguments_bound = (
                selection_contract is None
                or _coverage_result_arguments(contract, named_result, selection_contract[1], selection_contract[2])
            )
            header_arguments_bound = (
                header_contract is None
                or ((re.search(r"\brequires\b", contract) is None
                     or (entry["id"] == _JPIP_PHASE_ENTRY
                         and reference["symbol"] == "decode_automatic_precinct"
                         and len(re.findall(r"\brequires\b", contract)) == 1
                         and re.search(r"\brequires\s+start\s*<=\s*prefix\.len\(\)\s*,\s*ensures\b", contract)))
                    and _coverage_result_arguments(contract, named_result, header_contract[0], header_contract[3]))
            )
            statistic_arguments = {
                "Tier1PassStatistics::scanned": (0, "count"),
                "Tier1PassStatistics::decoded_symbols": (1, "count"),
                "Tier1PassStatistics::became_significant": (2, "1"),
                "Tier1PassStatistics::refined": (3, "1"),
            }.get(reference["symbol"]) if (
                reference["path"] == "src/tier1.rs" or reference["path"].startswith("src/tier1/")
            ) else None
            statistic_arguments_bound = (
                statistic_arguments is None
                or _coverage_result_arguments(
                    contract, named_result, "tier1_statistics_increment",
                    r"\*\s*old\(\s*self\s*\)\s*,\s*"
                    + str(statistic_arguments[0]) + r"\s*,\s*"
                    + re.escape(statistic_arguments[1]),
                )
            )
            if ("verus_spec(" not in contract
                    or (mutating and (state_result is None or not complete_state))
                    or not metadata_arguments_bound
                    or not palette_arguments_bound
                    or not cleanup_arguments_bound
                    or not refinement_arguments_bound
                    or not prepare_arguments_bound
                    or not component_arguments_bound
                    or not arbitrary_arguments_bound
                    or not packet_arguments_bound
                    or not selection_arguments_bound
                    or not header_arguments_bound
                    or not statistic_arguments_bound
                    or (expected_result_model is not None
                        and (named_result is None or named_result["model"] != expected_result_model))
                    or not ("ensures returns" in contract
                            or (named_result is not None and named_result["model"] in spec_symbols))):
                raise ValueError(f"linked function lacks executable Verus contract: {short}")
            if not any(re.search(rf"\b{re.escape(symbol)}\b", contract) for symbol in spec_symbols):
                raise ValueError(f"linked function contract lacks normative spec reference: {short}")
            main_header_caller = (
                main_header_contract and entry["id"] in ("part1-complete-native-raw-main-header-result", _RAW_LAYOUT_ENTRY)
            )
            exported_recovery_entry = (
                entry["id"] in _RAW_RECOVERY_PUBLIC_ENTRIES
                and (reference["path"], reference["symbol"]) ==
                    ("src/recovery.rs", _RAW_RECOVERY_PUBLIC_ENTRIES[entry["id"]])
                and re.search(
                    r"\bpub\s+fn\s+" + re.escape(_RAW_RECOVERY_PUBLIC_ENTRIES[entry["id"]]) + r"\b",
                    signature_match.group(),
                )
            )
            if claimed_consumer and not main_header_caller and not exported_recovery_entry and not any(
                ref != reference
                and (cross_file_call(
                    (ROOT / ref["path"]).resolve(), ref["symbol"], short,
                    require_caller_body=_coverage_named_caller_required(reference["path"]),
                )
                 if ref["path"] != reference["path"] else
                 same_file_call(path, ref["symbol"], short))
                for ref in entry["implementation_refs"]
            ):
                raise ValueError(f"linked function is not used by claimed implementation: {short}")
            if claimed_consumer:
                contract_functions.add((reference["path"], reference["symbol"]))
    return {
        "status": "passed",
        "inventory_items": len(ids),
        "referenced_contract_functions": len(contract_functions),
        "scope": coverage["scope"],
    }


def segment(marker: int, payload: bytes) -> bytes:
    return struct.pack(">HH", marker, len(payload) + 2) + payload


def box(box_type: bytes, payload: bytes) -> bytes:
    return struct.pack(">I4s", len(payload) + 8, box_type) + payload


def raw_codestream() -> bytes:
    siz = (
        struct.pack(">HIIIIIIIIH", 0, 1, 1, 0, 0, 1, 1, 0, 0, 1)
        + bytes((7, 1, 1))
    )
    data = b"\xff\x4f"
    data += segment(0xFF51, siz)
    data += segment(0xFF52, bytes((0, 0, 0, 1, 0, 0, 0, 0, 0, 1)))
    data += segment(0xFF5C, bytes((0, 0x40)))
    sot_offset = len(data)
    data += segment(0xFF90, struct.pack(">HI2B", 0, 15, 0, 1))
    data += b"\xff\x93\x00"
    assert len(data) - sot_offset == 15
    return data + b"\xff\xd9"


def jp2_file(
    codestream: bytes, brand: bytes = b"jp2 ", *,
    width: int = 1, height: int = 1, components: int = 1, precision: int = 8,
    signed: bool = False,
    color_space: int | None = None,
) -> bytes:
    if (width <= 0 or height <= 0 or components not in (1, 3)
            or not 1 <= precision <= 38 or type(signed) is not bool):
        raise ValueError("generated container requires positive geometry and uniform grayscale/RGB components")
    selected_color = (17 if components == 1 else 16) if color_space is None else color_space
    if selected_color not in (16, 17, 18):
        raise ValueError("generated container requires a supported enumerated color space")
    signature = box(b"jP  ", b"\x0d\x0a\x87\x0a")
    ftyp = box(b"ftyp", brand + b"\0\0\0\0" + brand)
    ihdr = box(b"ihdr", struct.pack(">IIH4B", height, width, components,
                                   (precision - 1) | (0x80 if signed else 0), 7, 0, 0))
    colr = box(b"colr", bytes((1, 0, 0, 0, 0, 0, selected_color)))
    return signature + ftyp + box(b"jp2h", ihdr + colr) + box(b"jp2c", codestream)


def jph_file() -> bytes:
    siz = (
        struct.pack(">HIIIIIIIIH", 0x4000, 1, 1, 0, 0, 1, 1, 0, 0, 1)
        + bytes((7, 1, 1))
    )
    codestream = b"\xff\x4f"
    codestream += segment(0xFF51, siz)
    codestream += segment(0xFF50, bytes((0, 2, 0, 0, 0, 8)))
    codestream += segment(0xFF52, bytes((0, 0, 0, 1, 0, 0, 0, 0, 0x40, 1)))
    codestream += segment(0xFF5C, bytes((0, 0x40)))
    codestream += segment(0xFF90, struct.pack(">HI2B", 0, 14, 0, 1))
    codestream += b"\xff\x93\xff\xd9"
    return jp2_file(codestream, b"jph ")


def jpx_file(codestream: bytes) -> bytes:
    signature = box(b"jP  ", b"\x0d\x0a\x87\x0a")
    ftyp = box(b"ftyp", b"jpxb\0\0\0\0jpxb")
    ihdr = box(b"ihdr", struct.pack(">IIH4B", 1, 1, 1, 7, 7, 0, 0))
    colr = box(b"colr", bytes((1, 0, 0, 0, 0, 0, 17)))
    return signature + ftyp + box(b"jp2h", ihdr + colr) + box(b"jp2c", codestream)


def jpip_response() -> bytes:
    # Explicit class/codestream form, one metadata byte, then EOR reason 1.
    return bytes((0x72, 0x08, 0x00, 0x00, 0x01, ord("x"), 0x00, 0x01, 0x00))


@dataclass(frozen=True)
class GeneratedCase:
    case_id: str
    format: str
    kind: str
    data: bytes
    expected: str
    operation: str = "decode"
    parent: str | None = None
    relation: str | None = None


def generated_cases() -> list[GeneratedCase]:
    raw = raw_codestream()
    jp2 = jp2_file(raw)
    jph = jph_file()
    jpx = jpx_file(raw)
    jpip = jpip_response()
    positives = [
        GeneratedCase("raw-minimal", "raw", "positive", raw, "accept"),
        GeneratedCase("jp2-minimal", "jp2", "positive", jp2, "accept"),
        GeneratedCase("jph-minimal-profile", "jph", "positive", jph, "accept", "inspect"),
        GeneratedCase("jpx-minimal", "jpx", "positive", jpx, "accept"),
        GeneratedCase("jpip-minimal-response", "jpip", "positive", jpip, "accept", "ingest"),
    ]
    cases = list(positives)
    for positive in positives:
        prefix_length = max(1, min(12, len(positive.data) // 2))
        cases.append(
            GeneratedCase(
                f"{positive.case_id}-truncated-prefix",
                positive.format,
                "malformed-prefix",
                positive.data[:prefix_length],
                "reject",
                positive.operation,
            )
        )
    cases.extend(
        [
            GeneratedCase(
                "raw-invalid-soc", "raw", "negative", b"\x00\x4f" + raw[2:], "reject"
            ),
            GeneratedCase(
                "jp2-invalid-signature",
                "jp2",
                "negative",
                jp2[:8] + b"\0\0\0\0" + jp2[12:],
                "reject",
            ),
            GeneratedCase(
                "jph-contradictory-brand",
                "jph",
                "negative",
                jph.replace(b"jph \0\0\0\0jph ", b"jph \0\0\0\0jp2 ", 1),
                "reject",
                "inspect",
            ),
            GeneratedCase(
                "jpx-invalid-box-length",
                "jpx",
                "negative",
                b"\0\0\0\x07" + jpx[4:],
                "reject",
            ),
            GeneratedCase(
                "jpip-overlong-vbas",
                "jpip",
                "negative",
                bytes((0x40, 0x80)),
                "reject",
                "ingest",
            ),
            GeneratedCase(
                "raw-comment-metamorphic",
                "raw",
                "metamorphic",
                raw[: raw.index(b"\xff\x90")]
                + segment(0xFF64, b"generated")
                + raw[raw.index(b"\xff\x90") :],
                "accept",
                parent="raw-minimal",
                relation="same-normalized-output",
            ),
            GeneratedCase(
                "jp2-free-box-metamorphic",
                "jp2",
                "metamorphic",
                jp2[:32] + box(b"free", b"generated") + jp2[32:],
                "accept",
                parent="jp2-minimal",
                relation="same-normalized-output",
            ),
        ]
    )
    return cases


def build_manifest(cases: list[GeneratedCase]) -> dict[str, Any]:
    entries = []
    for case in cases:
        suffix = {
            "raw": ".j2k",
            "jp2": ".jp2",
            "jph": ".jph",
            "jpx": ".jpx",
            "jpip": ".jpip",
        }[case.format]
        relative = f"generated/corpus/{case.case_id}{suffix}"
        entry: dict[str, Any] = {
            "id": case.case_id,
            "path": relative,
            "format": case.format,
            "kind": case.kind,
            "operation": case.operation,
            "expected": case.expected,
            "sha256": sha256_bytes(case.data),
            "bytes": len(case.data),
            "classification": "generated",
            "redistribution": "approved",
            "license": "project-generated-no-external-rights",
            "generator": {
                "id": GENERATOR_ID,
                "recipe": case.case_id,
                "inputs": [],
            },
        }
        if case.parent:
            entry["metamorphic"] = {"parent": case.parent, "relation": case.relation}
        entries.append(entry)
    return {
        "$schema": "./corpus.schema.json",
        "schema_version": 1,
        "profile_id": PROFILE_ID,
        "policy": {
            "official_vectors_included": False,
            "restricted_vectors_included": False,
            "allowed_classifications": ["generated"],
        },
        "generator": {
            "id": GENERATOR_ID,
            "source": "validation/framework.py",
            "deterministic": True,
        },
        "entries": entries,
    }


def generate_corpus(check: bool = False) -> dict[str, Any]:
    cases = generated_cases()
    manifest = build_manifest(cases)
    mismatches: list[str] = []
    for case, entry in zip(cases, manifest["entries"]):
        path = VALIDATION / entry["path"]
        if check:
            if not path.is_file() or path.read_bytes() != case.data:
                mismatches.append(entry["path"])
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(case.data)
    expected_manifest = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    if check:
        if not MANIFEST_PATH.is_file() or MANIFEST_PATH.read_text() != expected_manifest:
            mismatches.append(MANIFEST_PATH.relative_to(ROOT).as_posix())
        if mismatches:
            raise ValueError("generated corpus drift: " + ", ".join(mismatches))
    else:
        MANIFEST_PATH.write_text(expected_manifest)
    return manifest


def load_manifest() -> dict[str, Any]:
    return json.loads(MANIFEST_PATH.read_text())


def verify_manifest(manifest: dict[str, Any] | None = None) -> dict[str, Any]:
    manifest = manifest or load_manifest()
    errors: list[str] = []
    ids: set[str] = set()
    if manifest.get("schema_version") != 1:
        errors.append("unsupported schema_version")
    policy = manifest.get("policy", {})
    if policy.get("official_vectors_included") or policy.get("restricted_vectors_included"):
        errors.append("manifest may not include official or restricted vectors")
    entries = manifest.get("entries")
    if not isinstance(entries, list) or not entries:
        errors.append("entries must be a non-empty array")
        entries = []
    for entry in entries:
        case_id = entry.get("id")
        if not isinstance(case_id, str) or not case_id or case_id in ids:
            errors.append(f"invalid or duplicate id: {case_id!r}")
            continue
        ids.add(case_id)
        if entry.get("classification") != "generated":
            errors.append(f"{case_id}: only generated assets are permitted")
        if entry.get("redistribution") != "approved":
            errors.append(f"{case_id}: redistribution is not approved")
        if entry.get("generator", {}).get("id") != GENERATOR_ID:
            errors.append(f"{case_id}: unrecognized generator")
        relative = entry.get("path", "")
        path = (VALIDATION / relative).resolve()
        try:
            path.relative_to(CORPUS_DIR.resolve())
        except ValueError:
            errors.append(f"{case_id}: path escapes generated corpus")
            continue
        if not path.is_file():
            errors.append(f"{case_id}: missing file")
            continue
        data = path.read_bytes()
        if len(data) != entry.get("bytes"):
            errors.append(f"{case_id}: byte length mismatch")
        if sha256_bytes(data) != entry.get("sha256"):
            errors.append(f"{case_id}: SHA-256 mismatch")
    for entry in entries:
        relation = entry.get("metamorphic")
        if relation and relation.get("parent") not in ids:
            errors.append(f"{entry.get('id')}: unknown metamorphic parent")
    disk_files = {
        path.relative_to(VALIDATION).as_posix()
        for path in CORPUS_DIR.glob("*")
        if path.is_file()
    }
    manifest_files = {entry.get("path") for entry in entries}
    extras = sorted(disk_files - manifest_files)
    if extras:
        errors.append("unmanifested corpus files: " + ", ".join(extras))
    if errors:
        raise ValueError("; ".join(errors))
    return {
        "status": "passed",
        "entries": len(entries),
        "manifest_sha256": sha256_file(MANIFEST_PATH),
    }


def crop_image(observation: dict[str, Any], frame: tuple[int, int, int, int],
               rectangle: tuple[int, int, int, int], sampling: tuple[int, int] = (1, 1)) -> dict[str, Any]:
    x0, y0, x1, y1 = rectangle
    sx, sy = sampling
    image = observation.get("image")
    if (not observation.get("accepted") or not isinstance(image, dict) or not image.get("components")
            or sx <= 0 or sy <= 0
            or not frame[0] <= x0 < x1 <= frame[2] or not frame[1] <= y0 < y1 <= frame[3]):
        raise ValueError("reference crop requires an accepted image and a nonempty in-frame rectangle")
    result = copy.deepcopy(observation)
    result["image"]["width"] = x1 - x0
    result["image"]["height"] = y1 - y0
    for component in result["image"]["components"]:
        width, height = component["width"], component["height"]
        samples = component["samples"]
        cx0, cy0 = (frame[0] + sx - 1) // sx, (frame[1] + sy - 1) // sy
        cx1, cy1 = (frame[2] + sx - 1) // sx, (frame[3] + sy - 1) // sy
        if width != cx1 - cx0 or height != cy1 - cy0 or len(samples) != width * height:
            raise ValueError("reference crop component geometry or sample count differs from its frame")
        left, right = (x0 + sx - 1) // sx, (x1 + sx - 1) // sx
        top, bottom = (y0 + sy - 1) // sy, (y1 + sy - 1) // sy
        component["samples"] = [samples[(y - cy0) * width + x - cx0]
                                for y in range(top, bottom) for x in range(left, right)]
        component["width"], component["height"] = right - left, bottom - top
    return result


def parse_subject_output(stdout: bytes, stderr: bytes, returncode: int) -> dict[str, Any]:
    text = stdout.decode("utf-8", "replace").strip()
    if returncode != 0 and not text.startswith("ERR\t"):
        return {
            "accepted": False,
            "category": "process-error",
            "returncode": returncode,
            "stderr": stderr.decode("utf-8", "replace")[:4096],
            "execution_failed": True,
        }
    if text.startswith("ERR\t"):
        fields = text.split("\t", 2)
        return {
            "accepted": False,
            "category": fields[1] if len(fields) > 1 else "unknown",
        }
    if text.startswith("META\t"):
        return {"accepted": True, "metadata": text.split("\t")[1:]}
    lines = text.splitlines()
    if len(lines) < 2 or lines[0] != "IMAGE":
        return {"accepted": False, "category": "invalid-harness-output", "execution_failed": True}
    header = [int(value) for value in lines[1].split()]
    components = []
    for line in lines[2:]:
        fields = line.split("\t")
        samples = [] if len(fields) < 6 or not fields[5] else [
            int(value) for value in fields[5].split(",")
        ]
        components.append(
            {
                "width": int(fields[0]),
                "height": int(fields[1]),
                "precision": int(fields[2]),
                "signed": fields[3] == "1",
                "sample_kind": fields[4],
                "samples": samples,
            }
        )
    return {
        "accepted": True,
        "image": {
            "width": header[0],
            "height": header[1],
            "components": components,
        },
    }


def parse_pnm(path: Path) -> dict[str, Any]:
    data = path.read_bytes()
    offset = 0

    def token() -> bytes:
        nonlocal offset
        while offset < len(data):
            if data[offset : offset + 1] == b"#":
                offset = data.find(b"\n", offset)
                if offset < 0:
                    raise ValueError("unterminated PNM comment")
            elif data[offset : offset + 1].isspace():
                offset += 1
            else:
                break
        start = offset
        while offset < len(data) and not data[offset : offset + 1].isspace():
            offset += 1
        return data[start:offset]

    magic = token()
    if magic not in (b"P5", b"P6"):
        raise ValueError("only binary PGM/PPM outputs are supported")
    width, height, maximum = int(token()), int(token()), int(token())
    if offset >= len(data) or not data[offset : offset + 1].isspace():
        raise ValueError("missing PNM header delimiter")
    offset += 1
    if data[offset - 1 : offset] == b"\r" and data[offset : offset + 1] == b"\n":
        offset += 1
    channels = 1 if magic == b"P5" else 3
    sample_bytes = 1 if maximum < 256 else 2
    expected = width * height * channels * sample_bytes
    payload = data[offset:]
    if len(payload) != expected:
        raise ValueError("PNM payload length mismatch")
    values = list(payload) if sample_bytes == 1 else [
        int.from_bytes(payload[index : index + 2], "big")
        for index in range(0, len(payload), 2)
    ]
    components = []
    for channel in range(channels):
        components.append(
            {
                "width": width,
                "height": height,
                "precision": maximum.bit_length(),
                "signed": False,
                "sample_kind": "unsigned",
                "samples": values[channel::channels],
            }
        )
    return {
        "accepted": True,
        "image": {"width": width, "height": height, "components": components},
    }


def parse_pgx(path: Path) -> dict[str, Any]:
    header, delimiter, payload = path.read_bytes().partition(b"\n")
    fields = header.split()
    if (not delimiter or len(fields) != 6 or fields[0] != b"PG"
            or fields[1] not in (b"ML", b"LM") or fields[2] not in (b"+", b"-")):
        raise ValueError("invalid binary PGX header")
    precision, width, height = (int(value) for value in fields[3:])
    if not 1 <= precision <= 32 or width <= 0 or height <= 0:
        raise ValueError("PGX precision or geometry is outside the supported profile")
    sample_bytes = 1 if precision <= 8 else 2 if precision <= 16 else 4
    if len(payload) != width * height * sample_bytes:
        raise ValueError("PGX payload length mismatch")
    signed = fields[2] == b"-"
    byteorder = "big" if fields[1] == b"ML" else "little"
    values = [
        int.from_bytes(payload[index:index + sample_bytes], byteorder, signed=signed)
        for index in range(0, len(payload), sample_bytes)
    ]
    lower = -(1 << (precision - 1)) if signed else 0
    upper = lower + (1 << precision) - 1
    if any(not lower <= value <= upper for value in values):
        raise ValueError("PGX sample exceeds declared precision")
    return {
        "accepted": True,
        "image": {"width": width, "height": height, "components": [{
            "width": width, "height": height, "precision": precision,
            "signed": signed, "sample_kind": "signed" if signed else "unsigned",
            "samples": values,
        }]},
    }


def parse_pfm_bit_patterns(path: Path) -> dict[str, Any]:
    """Read binary32 words in stored scanline order, not floating-point values."""
    fields = path.read_bytes().split(b"\n", 3)
    if len(fields) != 4 or fields[0] not in (b"Pf", b"PF"):
        raise ValueError("invalid binary32 PFM fixture header")
    dimensions = fields[1].split()
    if len(dimensions) != 2:
        raise ValueError("invalid PFM fixture dimensions")
    width, height = (int(value) for value in dimensions)
    scale = float(fields[2])
    if width <= 0 or height <= 0 or scale not in (-1.0, 1.0):
        raise ValueError("PFM fixture requires positive dimensions and unit scale")
    channels = 1 if fields[0] == b"Pf" else 3
    payload = fields[3]
    if len(payload) != width * height * channels * 4:
        raise ValueError("PFM fixture payload length mismatch")
    values = [value for (value,) in struct.iter_unpack("<i" if scale < 0 else ">i", payload)]
    return {
        "accepted": True,
        "image": {"width": width, "height": height, "components": [{
            "width": width, "height": height, "precision": 32,
            "signed": True, "sample_kind": "signed", "samples": values[channel::channels],
        } for channel in range(channels)]},
    }


def normalized_hash(outcome: dict[str, Any]) -> str:
    stable = {
        key: value
        for key, value in outcome.items()
        if key not in {"elapsed_ms", "stderr", "returncode"}
    }
    return sha256_bytes(canonical_bytes(stable))


def disagreement_id(disagreement: dict[str, Any]) -> str:
    identity = {
        key: disagreement.get(key)
        for key in (
            "case_id",
            "oracle",
            "kind",
            "subject_sha256",
            "oracle_sha256",
        )
    }
    return "oracle-disagreement-v1:" + sha256_bytes(canonical_bytes(identity))


def build_adjudications(
    disagreements: list[dict[str, Any]],
    validation_result: Path,
    external_oracles_available: int,
    adjudication_file: Path | None = None,
    external_observations: int = 0,
    external_oracle_errors: int = 0,
) -> dict[str, Any]:
    previous: dict[str, dict[str, Any]] = {}
    if adjudication_file is not None:
        existing = json.loads(adjudication_file.read_text())
        validate_schema(VALIDATION / "oracle-adjudication.schema.json", existing)
        if len({record["id"] for record in existing["records"]}) != len(existing["records"]):
            raise ValueError("duplicate external adjudication identifier")
        previous = {
            record["id"]: record
            for record in existing["records"]
        }
    records = []
    for disagreement in disagreements:
        record_id = disagreement_id(disagreement)
        retained = previous.get(record_id, {})
        if retained and disagreement_id(retained) != record_id:
            raise ValueError("external adjudication does not match observation identity")
        records.append(
            {
                "id": record_id,
                **{
                    key: disagreement.get(key)
                    for key in (
                        "case_id",
                        "oracle",
                        "kind",
                        "subject_sha256",
                        "oracle_sha256",
                    )
                },
                "status": retained.get("status", "unadjudicated"),
                "decision": retained.get("decision"),
                "rationale": retained.get("rationale"),
                "adjudicator": retained.get("adjudicator"),
                "adjudicated_at": retained.get("adjudicated_at"),
            }
        )
    unresolved = sum(record["status"] == "unadjudicated" for record in records)
    status = (
        "blocked"
        if external_oracle_errors
        else "skipped"
        if external_observations == 0
        else "passed"
        if unresolved == 0
        else "blocked"
    )
    return {
        "$schema": report_schema(validation_result.parent, "oracle-adjudication.schema.json"),
        "schema_version": 1,
        "status": status,
        "validation_result_sha256": sha256_file(validation_result),
        "summary": {
            "external_oracles_available": external_oracles_available,
            "external_observations": external_observations,
            "external_oracle_errors": external_oracle_errors,
            "total": len(records),
            "unadjudicated": unresolved,
            "adjudicated": len(records) - unresolved,
        },
        "records": records,
    }


def resolve_subject() -> Path:
    suffix = ".exe" if os.name == "nt" else ""
    return ROOT / "target" / "debug" / "examples" / f"validation_decoder{suffix}"


def build_subject(release: bool = False) -> Path:
    subprocess.run(
        ["cargo", "build", "--example", "validation_decoder", "--locked",
         *(["--release"] if release else [])],
        cwd=ROOT,
        check=True,
    )
    executable = (ROOT / "target" / "release" / "examples" / resolve_subject().name
                  if release else resolve_subject())
    if not executable.is_file():
        raise FileNotFoundError(f"subject harness not built: {executable}")
    return executable


def _official_source_url() -> str:
    return "https://handle.itu.int/11.1002/2000/6179"


def _official_limits(
    max_case_ms: float,
    max_total_ms: float,
    max_input_bytes: int,
    max_output_bytes: int,
    max_address_space_bytes: int,
) -> dict[str, Any]:
    return {
        "max_case_ms": max_case_ms,
        "max_total_ms": max_total_ms,
        "max_input_bytes": max_input_bytes,
        "max_output_bytes": max_output_bytes,
        "max_address_space_bytes": max_address_space_bytes,
        "memory_enforcement": (
            "POSIX RLIMIT_AS"
            if resource is not None and hasattr(resource, "RLIMIT_AS")
            else "unavailable on this platform; decoder ResourceLimits remain active"
        ),
    }


def _official_blocked_result(
    access_status: str,
    blocker: str,
    final_url: str | None,
    http_status: int | None,
    limits: dict[str, Any],
    output_dir: Path | None = None,
) -> dict[str, Any]:
    provenance = source_binding()
    source_revision = provenance["source_revision"]
    result = {
        "$schema": report_schema(output_dir, "official-vector-result.schema.json"),
        "schema_version": 1,
        "profile_id": PROFILE_ID,
        "status": "blocked",
        "source_url": _official_source_url(),
        "acquisition": {
            "attempted_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
            "access_status": access_status,
            "final_url": final_url,
            "http_status": http_status,
            "archive_sha256": None,
            "archive_bytes": None,
        },
        "manifest_sha256": None,
        "source_revision": source_revision,
        "provenance": provenance,
        "tool_revision": (
            f"python {sys.version_info.major}.{sys.version_info.minor}."
            f"{sys.version_info.micro}"
        ),
        "subject": {
            "binary_sha256": None,
            "source_revision": source_revision,
        },
        "selection": {"complete": False, "applicable": 0, "inapplicable": 0},
        "summary": {
            "verified": 0,
            "executed": 0,
            "passed": 0,
            "failed": 0,
            "blocked": 0,
            "total_elapsed_ms": 0.0,
        },
        "limits": limits,
        "blockers": [blocker],
        "records": [],
    }
    validate_schema(VALIDATION / "official-vector-result.schema.json", result)
    write_json(report_path(output_dir, "official-vector-results.json"), result)
    return result


def _external_path(root: Path, relative: str) -> Path:
    candidate = (root / relative).resolve()
    try:
        candidate.relative_to(root.resolve())
    except ValueError as error:
        raise ValueError("official vector manifest path escapes external root") from error
    return candidate


def _image_metrics(outcome: dict[str, Any]) -> dict[str, Any] | None:
    image = outcome.get("image")
    if not isinstance(image, dict):
        return None
    return {
        "width": image["width"],
        "height": image["height"],
        "components": [
            {
                key: component[key]
                for key in ("width", "height", "precision", "signed", "sample_kind")
            }
            for component in image["components"]
        ],
    }


def _run_process_bounded_threaded(
    command: list[str],
    timeout_seconds: float,
    max_output_bytes: int,
) -> tuple[subprocess.CompletedProcess[bytes], float, bool]:
    start = time.monotonic()
    process = subprocess.Popen(
        command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0,
    )
    streams = {"stdout": process.stdout, "stderr": process.stderr}
    output = {"stdout": bytearray(), "stderr": bytearray()}
    events: queue.Queue[tuple[str, bytes | OSError | ValueError]] = queue.Queue(maxsize=4)
    stopped = threading.Event()
    readers = []

    def publish(name: str, data: bytes | OSError | ValueError) -> None:
        while not stopped.is_set():
            try:
                events.put((name, data), timeout=0.05)
                return
            except queue.Full:
                continue

    def read_stream(name: str, stream: BinaryIO) -> None:
        try:
            while not stopped.is_set():
                chunk = stream.read(64 * 1024)
                publish(name, chunk)
                if not chunk:
                    return
        except (OSError, ValueError) as error:
            publish(name, error)

    output_limited = False
    try:
        for name, stream in streams.items():
            if stream is not None:
                reader = threading.Thread(target=read_stream, args=(name, stream),
                                          name=f"jpeg2000-capture-{name}", daemon=True)
                reader.start()
                readers.append(reader)
        closed = 0
        while closed < len(readers):
            remaining = timeout_seconds - (time.monotonic() - start)
            if remaining <= 0:
                raise subprocess.TimeoutExpired(command, timeout_seconds)
            try:
                name, chunk = events.get(timeout=min(remaining, 0.1))
            except queue.Empty:
                continue
            if isinstance(chunk, (OSError, ValueError)):
                raise chunk
            if not chunk:
                closed += 1
                continue
            if len(output["stdout"]) + len(output["stderr"]) + len(chunk) > max_output_bytes:
                output_limited = True
                break
            output[name].extend(chunk)
        if not output_limited:
            remaining = timeout_seconds - (time.monotonic() - start)
            try:
                process.wait(timeout=max(remaining, 0.001))
            except subprocess.TimeoutExpired:
                raise subprocess.TimeoutExpired(command, timeout_seconds) from None
    finally:
        stopped.set()
        if process.poll() is None:
            process.kill()
        process.wait()
        for stream in streams.values():
            if stream is not None:
                stream.close()
        for reader in readers:
            reader.join(timeout=1.0)
        if any(reader.is_alive() for reader in readers):
            raise RuntimeError("bounded process capture did not shut down its pipe readers")
    completed = subprocess.CompletedProcess(
        command, process.returncode, bytes(output["stdout"]), bytes(output["stderr"]),
    )
    return completed, (time.monotonic() - start) * 1000, output_limited


def _run_process_bounded(
    command: list[str],
    timeout_seconds: float,
    max_output_bytes: int,
    preexec_fn: Any,
) -> tuple[subprocess.CompletedProcess[bytes], float, bool]:
    if sys.platform == "win32":
        if preexec_fn is not None:
            raise ValueError("POSIX process setup is not supported on Windows")
        return _run_process_bounded_threaded(command, timeout_seconds, max_output_bytes)
    start = time.monotonic()
    process = subprocess.Popen(
        command,
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        preexec_fn=preexec_fn,
    )
    streams = {"stdout": process.stdout, "stderr": process.stderr}
    output = {"stdout": bytearray(), "stderr": bytearray()}
    selector = selectors.DefaultSelector()
    for name, stream in streams.items():
        if stream is not None:
            selector.register(stream, selectors.EVENT_READ, name)
    output_limited = False
    try:
        while selector.get_map():
            remaining = timeout_seconds - (time.monotonic() - start)
            if remaining <= 0:
                process.kill()
                process.wait()
                raise subprocess.TimeoutExpired(command, timeout_seconds)
            for key, _ in selector.select(min(remaining, 0.1)):
                chunk = os.read(key.fileobj.fileno(), 64 * 1024)
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                current_bytes = len(output["stdout"]) + len(output["stderr"])
                if current_bytes + len(chunk) > max_output_bytes:
                    output_limited = True
                    process.kill()
                    for stream in streams.values():
                        if stream is not None:
                            stream.close()
                    process.wait()
                    break
                output[key.data].extend(chunk)
            if output_limited:
                break
        if not output_limited:
            remaining = timeout_seconds - (time.monotonic() - start)
            try:
                process.wait(timeout=max(remaining, 0.001))
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
                raise subprocess.TimeoutExpired(command, timeout_seconds)
    finally:
        selector.close()
        for stream in streams.values():
            if stream is not None and not stream.closed:
                stream.close()
    completed = subprocess.CompletedProcess(
        command,
        process.returncode,
        bytes(output["stdout"]),
        bytes(output["stderr"]),
    )
    return completed, (time.monotonic() - start) * 1000, output_limited


def run_official_vectors(
    executable: Path | None = None,
    vector_root: Path | None = None,
    manifest_path: Path | None = None,
    *,
    access_status: str = "not-configured",
    blocked_reason: str = "official vector root is not configured",
    final_url: str | None = None,
    http_status: int | None = None,
    max_case_ms: float = 10000.0,
    max_total_ms: float = 300000.0,
    max_input_bytes: int = 64 * 1024 * 1024,
    max_output_bytes: int = 64 * 1024 * 1024,
    max_address_space_bytes: int = 512 * 1024 * 1024,
    output_dir: Path | None = None,
) -> dict[str, Any]:
    """Verify and execute externally held official vectors without copying them."""
    if any(not math.isfinite(limit) or limit <= 0 for limit in (
        max_case_ms, max_total_ms, max_input_bytes,
        max_output_bytes, max_address_space_bytes,
    )):
        raise ValueError("official vector limits must be positive")
    limits = _official_limits(
        max_case_ms,
        max_total_ms,
        max_input_bytes,
        max_output_bytes,
        max_address_space_bytes,
    )
    configured_root = vector_root or (
        Path(os.environ[OFFICIAL_VECTOR_ROOT_ENV])
        if os.environ.get(OFFICIAL_VECTOR_ROOT_ENV)
        else None
    )
    if configured_root is None:
        return _official_blocked_result(
            access_status, blocked_reason, final_url, http_status, limits, output_dir
        )
    root = configured_root.resolve()
    if not root.is_dir():
        return _official_blocked_result(
            "unavailable",
            "configured official vector root is not an accessible directory",
            final_url,
            http_status,
            limits,
            output_dir,
        )
    configured_manifest = manifest_path or (
        Path(os.environ[OFFICIAL_VECTOR_MANIFEST_ENV])
        if os.environ.get(OFFICIAL_VECTOR_MANIFEST_ENV)
        else root / "official-vector-manifest.json"
    )
    if not configured_manifest.is_file():
        return _official_blocked_result(
            "unavailable",
            "external official vector manifest is unavailable",
            final_url,
            http_status,
            limits,
            output_dir,
        )
    manifest_bytes = configured_manifest.read_bytes()
    try:
        manifest = json.loads(manifest_bytes)
        validate_schema(VALIDATION / "official-vector-manifest.schema.json", manifest)
    except (json.JSONDecodeError, ValueError) as error:
        raise ValueError(f"invalid external official vector manifest: {error}") from error
    suite = manifest["suite"]
    entries = manifest["entries"]
    applicable = [entry for entry in entries if entry["applicable"]]
    if suite["selection"]["applicable_vector_count"] != len(applicable):
        raise ValueError("applicable official vector count does not match selection")
    ids = [entry["id"] for entry in entries]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate official vector identifier")
    for entry in entries:
        _external_path(root, entry["path"])

    archive = suite["archive"]
    archive_path = _external_path(root, archive["path"])
    archive_valid = (
        archive_path.is_file()
        and archive_path.stat().st_size == archive["bytes"]
        and sha256_file(archive_path) == archive["sha256"]
    )
    blockers: list[str] = []
    if not archive_valid:
        blockers.append("official vector archive hash or byte length does not match manifest")

    if executable is None:
        executable = build_subject()
    provenance = source_binding()
    source_revision = provenance["source_revision"]
    records: list[dict[str, Any]] = []
    verified = 0
    executed = 0
    total_elapsed_ms = 0.0
    for entry in applicable:
        vector_path = _external_path(root, entry["path"])
        vector_key = "official-vector-v1:" + sha256_bytes(
            canonical_bytes({"id": entry["id"], "sha256": entry["sha256"]})
        )
        record: dict[str, Any] = {
            "vector_key": vector_key,
            "file_sha256": entry["sha256"],
            "bytes": entry["bytes"],
            "format": entry["format"],
            "status": "blocked",
            "accepted": None,
            "category": None,
            "normalized_output_sha256": None,
            "metrics": None,
            "elapsed_ms": 0.0,
            "failure": None,
        }
        if entry["identifier_public"]:
            record["public_id"] = entry["id"]
        if not archive_valid:
            record["failure"] = "archive integrity check failed; vector not executed"
            records.append(record)
            continue
        if not vector_path.is_file():
            record["failure"] = "vector file unavailable"
            records.append(record)
            continue
        actual_bytes = vector_path.stat().st_size
        actual_sha256 = sha256_file(vector_path)
        if actual_bytes != entry["bytes"] or actual_sha256 != entry["sha256"]:
            record["status"] = "failed"
            record["failure"] = "vector file hash or byte length mismatch"
            records.append(record)
            continue
        verified += 1
        if actual_bytes > max_input_bytes:
            record["status"] = "failed"
            record["failure"] = "input resource limit exceeded"
            records.append(record)
            continue
        if total_elapsed_ms >= max_total_ms:
            record["failure"] = "total execution time limit exhausted"
            records.append(record)
            continue

        preexec_fn = None
        if resource is not None and hasattr(resource, "RLIMIT_AS"):
            def limit_address_space() -> None:
                resource.setrlimit(
                    resource.RLIMIT_AS,
                    (max_address_space_bytes, max_address_space_bytes),
                )

            preexec_fn = limit_address_space
        command = [
            str(executable),
            entry["operation"],
            entry["format"],
            str(vector_path),
        ]
        start = time.monotonic()
        try:
            completed, elapsed_ms, output_limited = _run_process_bounded(
                command,
                min(max_case_ms, max_total_ms - total_elapsed_ms) / 1000,
                max_output_bytes,
                preexec_fn,
            )
            executed += 1
            if output_limited:
                outcome = {"accepted": False, "category": "output-limit"}
                record["failure"] = "output resource limit exceeded"
            else:
                outcome = parse_subject_output(
                    completed.stdout, completed.stderr, completed.returncode
                )
        except subprocess.TimeoutExpired:
            elapsed_ms = (time.monotonic() - start) * 1000
            executed += 1
            outcome = {"accepted": False, "category": "timeout"}
            record["failure"] = "execution time limit exceeded"
        except (OSError, ValueError) as error:
            elapsed_ms = (time.monotonic() - start) * 1000
            executed += 1
            outcome = {"accepted": False, "category": "harness-error"}
            record["failure"] = type(error).__name__
        elapsed_ms = round(elapsed_ms, 3)
        total_elapsed_ms += elapsed_ms
        output_sha256 = normalized_hash(outcome)
        expected = entry["expected"]
        failure = record["failure"]
        if outcome.get("execution_failed"):
            failure = "subject harness failed"
        elif outcome["accepted"] != expected["accepted"]:
            failure = "acceptance mismatch"
        elif outcome["accepted"] and output_sha256 != expected["normalized_sha256"]:
            failure = "normalized output hash mismatch"
        elif (
            not outcome["accepted"]
            and expected.get("category") is not None
            and outcome.get("category") != expected["category"]
        ):
            failure = "rejection category mismatch"
        record.update(
            {
                "status": "failed" if failure else "passed",
                "accepted": outcome["accepted"],
                "category": outcome.get("category"),
                "normalized_output_sha256": output_sha256,
                "metrics": _image_metrics(outcome),
                "elapsed_ms": elapsed_ms,
                "failure": failure,
            }
        )
        records.append(record)

    failed = sum(record["status"] == "failed" for record in records)
    blocked = sum(record["status"] == "blocked" for record in records)
    passed = sum(record["status"] == "passed" for record in records)
    if not archive_valid or failed:
        status = "failed"
    elif blocked:
        status = "blocked"
    elif not applicable or executed != len(applicable) or passed != len(applicable):
        status = "blocked"
    else:
        status = "passed"
    if status != "passed" and not blockers:
        blockers.append("not all selected-profile applicable official vectors passed")
    result = {
        "$schema": report_schema(output_dir, "official-vector-result.schema.json"),
        "schema_version": 1,
        "profile_id": PROFILE_ID,
        "status": status,
        "source_url": suite["source_url"],
        "acquisition": {
            "attempted_at": suite["acquired_at"],
            "access_status": "acquired",
            "final_url": suite["source_url"],
            "http_status": 200,
            "archive_sha256": archive["sha256"],
            "archive_bytes": archive["bytes"],
        },
        "manifest_sha256": sha256_bytes(manifest_bytes),
        "source_revision": source_revision,
        "provenance": provenance,
        "license": suite["license"],
        "tool_revision": (
            f"python {sys.version_info.major}.{sys.version_info.minor}."
            f"{sys.version_info.micro}; rust subject {sha256_file(executable)}"
        ),
        "subject": {
            "binary_sha256": sha256_file(executable),
            "source_revision": source_revision,
        },
        "selection": {
            "complete": suite["selection"]["complete"],
            "applicable": len(applicable),
            "inapplicable": len(entries) - len(applicable),
        },
        "summary": {
            "verified": verified,
            "executed": executed,
            "passed": passed,
            "failed": failed,
            "blocked": blocked,
            "total_elapsed_ms": round(total_elapsed_ms, 3),
        },
        "limits": limits,
        "blockers": blockers,
        "records": records,
    }
    validate_schema(VALIDATION / "official-vector-result.schema.json", result)
    write_json(report_path(output_dir, "official-vector-results.json"), result)
    return result


def load_oracles(path: Path | None = None) -> list[dict[str, Any]]:
    config_path = path or VALIDATION / "oracles.json"
    config = json.loads(config_path.read_text())
    validate_schema(VALIDATION / "oracle-config.schema.json", config)
    names = [spec["name"] for spec in config["oracles"]]
    if len(names) != len(set(names)):
        raise ValueError("duplicate oracle name")
    return config["oracles"]


def _run_process(command: list[str], timeout_seconds: float) -> tuple[subprocess.CompletedProcess[bytes], float]:
    completed, elapsed, limited = _run_process_bounded(command, timeout_seconds, 1024 * 1024, None)
    if limited:
        raise ValueError("process output limit exceeded")
    return completed, elapsed


def run_validation(
    executable: Path,
    include_external: bool = True,
    timeout_seconds: float = 5.0,
    oracle_config: Path | None = None,
    output_dir: Path | None = None,
    adjudication_file: Path | None = None,
) -> dict[str, Any]:
    if not math.isfinite(timeout_seconds) or timeout_seconds <= 0:
        raise ValueError("timeout must be positive")
    manifest = load_manifest()
    verify_manifest(manifest)
    oracle_specs = load_oracles(oracle_config) if include_external else []
    oracle_status: list[dict[str, Any]] = [
        {
            "name": "jpeg2000_rs",
            "status": "available",
            "executable": "cargo-example:validation_decoder",
            "binary_sha256": sha256_file(executable),
        }
    ]
    available_oracles: list[tuple[dict[str, Any], str]] = []
    oracle_errors: list[dict[str, Any]] = []
    for spec in oracle_specs:
        configured = os.environ.get(spec["environment"])
        found = configured or shutil.which(spec["executable"])
        if found and Path(found).is_file() and os.access(found, os.X_OK):
            available_oracles.append((spec, found))
            oracle_status.append(
                {
                    "name": spec["name"],
                    "status": "available",
                    "executable": Path(found).name,
                    "binary_sha256": sha256_file(Path(found).resolve()),
                }
            )
        elif configured:
            oracle_errors.append({"oracle": spec["name"], "reason": "configured executable unavailable"})
            oracle_status.append({
                "name": spec["name"], "status": "failed",
                "reason": "configured executable unavailable",
            })
        else:
            oracle_status.append(
                {
                    "name": spec["name"],
                    "status": "skipped",
                    "reason": f"{spec['environment']} unset and {spec['executable']} not found",
                }
            )
    records: list[dict[str, Any]] = []
    by_case: dict[str, dict[str, Any]] = {}
    for entry in manifest["entries"]:
        input_path = VALIDATION / entry["path"]
        command = [str(executable), entry["operation"], entry["format"], str(input_path)]
        try:
            process, elapsed = _run_process(command, timeout_seconds)
            outcome = parse_subject_output(process.stdout, process.stderr, process.returncode)
        except (subprocess.TimeoutExpired, OSError, ValueError) as error:
            elapsed = timeout_seconds * 1000
            outcome = {
                "accepted": False,
                "category": "timeout" if isinstance(error, subprocess.TimeoutExpired) else "harness-error",
                "execution_failed": True,
            }
        outcome["elapsed_ms"] = round(elapsed, 3)
        outcome["normalized_sha256"] = normalized_hash(outcome)
        record: dict[str, Any] = {
            "case_id": entry["id"],
            "expected": entry["expected"],
            "kind": entry["kind"],
            "format": entry["format"],
            "outcomes": {"jpeg2000_rs": outcome},
        }
        by_case[entry["id"]] = record
        for spec, oracle_executable in available_oracles:
            if entry["format"] not in spec["formats"] or entry["operation"] != "decode":
                record["outcomes"][spec["name"]] = {
                    "status": "skipped",
                    "reason": "unsupported format or operation",
                }
                continue
            output_base = report_path(output_dir, f"oracle-output/{spec['name']}-{entry['id']}")
            output_base.parent.mkdir(parents=True, exist_ok=True)
            output_path = output_base.with_suffix(".pnm")
            if output_path.exists():
                output_path.unlink()
            command = [
                value.format(
                    executable=oracle_executable,
                    input=str(input_path),
                    output=str(output_path),
                    format=entry["format"],
                )
                for value in spec["command"]
            ]
            try:
                process, oracle_elapsed = _run_process(command, timeout_seconds)
                if process.returncode == 0 and output_path.is_file():
                    oracle_outcome = parse_pnm(output_path)
                elif process.returncode > 0:
                    oracle_outcome = {
                        "accepted": False,
                        "category": "decoder-rejected",
                        "returncode": process.returncode,
                    }
                else:
                    raise ValueError("oracle succeeded without output or was terminated by signal")
                oracle_outcome["elapsed_ms"] = round(oracle_elapsed, 3)
                oracle_outcome["normalized_sha256"] = normalized_hash(oracle_outcome)
            except (subprocess.TimeoutExpired, OSError, ValueError) as error:
                oracle_outcome = {
                    "accepted": False,
                    "category": "timeout" if isinstance(error, subprocess.TimeoutExpired) else "output-error",
                    "execution_failed": True,
                }
                oracle_errors.append({
                    "oracle": spec["name"], "case_id": entry["id"],
                    "reason": oracle_outcome["category"],
                })
            finally:
                if output_path.exists():
                    output_path.unlink()
            record["outcomes"][spec["name"]] = oracle_outcome
        records.append(record)
    disagreements: list[dict[str, Any]] = []
    failures: list[dict[str, Any]] = []
    for entry, record in zip(manifest["entries"], records):
        subject = record["outcomes"]["jpeg2000_rs"]
        expected_accept = entry["expected"] == "accept"
        if subject.get("execution_failed") or subject["accepted"] != expected_accept:
            failures.append(
                {
                    "case_id": entry["id"],
                    "expected": entry["expected"],
                    "actual": "accept" if subject["accepted"] else "reject",
                    "category": subject.get("category"),
                }
            )
        relation = entry.get("metamorphic")
        if relation and subject["accepted"]:
            parent = by_case[relation["parent"]]["outcomes"]["jpeg2000_rs"]
            if subject.get("normalized_sha256") != parent.get("normalized_sha256"):
                failures.append(
                    {
                        "case_id": entry["id"],
                        "expected": relation["relation"],
                        "actual": "normalized-output-differs",
                    }
                )
        for oracle_name, oracle_outcome in record["outcomes"].items():
            if (
                oracle_name == "jpeg2000_rs"
                or "accepted" not in oracle_outcome
                or oracle_outcome.get("execution_failed")
            ):
                continue
            acceptance_differs = oracle_outcome["accepted"] != subject["accepted"]
            output_differs = (
                oracle_outcome["accepted"]
                and subject["accepted"]
                and oracle_outcome.get("normalized_sha256") != subject.get("normalized_sha256")
            )
            if acceptance_differs or output_differs:
                disagreement = {
                        "case_id": entry["id"],
                        "oracle": oracle_name,
                        "kind": "acceptance" if acceptance_differs else "normalized-output",
                        "subject_sha256": subject.get("normalized_sha256"),
                        "oracle_sha256": oracle_outcome.get("normalized_sha256"),
                        "status": "unadjudicated",
                    }
                disagreement["id"] = disagreement_id(disagreement)
                disagreements.append(disagreement)
    result = {
        "$schema": report_schema(output_dir, "validation-result.schema.json"),
        "schema_version": 1,
        "profile_id": PROFILE_ID,
        "provenance": source_binding(),
        "corpus_manifest_sha256": sha256_file(MANIFEST_PATH),
        "oracle_config_sha256": sha256_file(oracle_config or VALIDATION / "oracles.json") if include_external else None,
        "oracles": oracle_status,
        "summary": {
            "cases": len(records),
            "passed": len(records) - len(failures),
            "failed": len(failures),
            "disagreements": len(disagreements),
            "external_oracles_available": len(available_oracles),
            "external_oracles_skipped": sum(
                status["status"] == "skipped" for status in oracle_status
            ),
            "oracle_errors": len(oracle_errors),
        },
        "failures": failures,
        "oracle_errors": oracle_errors,
        "disagreements": disagreements,
        "records": records,
    }
    validation_path = report_path(output_dir, "validation-results.json")
    result["summary"]["status"] = "failed" if failures or oracle_errors else "blocked" if disagreements else "passed"
    write_json(validation_path, result)
    write_json(
        report_path(output_dir, "disagreements.json"),
        {
            "schema_version": 1,
            "status": "blocked" if disagreements else "passed" if available_oracles else "skipped",
            "disagreements": disagreements,
        },
    )
    adjudications = build_adjudications(
        disagreements,
        validation_path,
        len(available_oracles),
        adjudication_file,
        external_observations=sum(
            "accepted" in outcome and not outcome.get("execution_failed")
            for record in records
            for name, outcome in record["outcomes"].items()
            if name != "jpeg2000_rs"
        ),
        external_oracle_errors=len(oracle_errors),
    )
    write_json(report_path(output_dir, "oracle-adjudications.json"), adjudications)
    if result["summary"]["status"] == "blocked" and adjudications["status"] == "passed":
        result["summary"]["status"] = "passed"
        write_json(validation_path, result)
        adjudications["validation_result_sha256"] = sha256_file(validation_path)
        write_json(report_path(output_dir, "oracle-adjudications.json"), adjudications)
    return result


def run_budget(
    executable: Path,
    max_case_ms: float = 5000.0,
    max_total_ms: float = 30000.0,
    max_output_bytes: int = 1024 * 1024,
    max_input_bytes: int = 1024 * 1024,
    max_address_space_bytes: int = 512 * 1024 * 1024,
    output_dir: Path | None = None,
) -> dict[str, Any]:
    if any(not math.isfinite(limit) or limit <= 0 for limit in (
        max_case_ms, max_total_ms, max_output_bytes,
        max_input_bytes, max_address_space_bytes,
    )):
        raise ValueError("budgets must be positive")
    manifest = load_manifest()
    verify_manifest(manifest)
    cases: list[dict[str, Any]] = []
    total_ms = 0.0
    failures: list[str] = []
    for entry in manifest["entries"]:
        input_path = VALIDATION / entry["path"]
        if entry["bytes"] > max_input_bytes or total_ms >= max_total_ms:
            reason = "input budget" if entry["bytes"] > max_input_bytes else "total time budget"
            failures.append(f"{entry['id']}: {reason}")
            cases.append({"case_id": entry["id"], "elapsed_ms": 0.0, "output_bytes": 0, "status": "failed"})
            continue
        command = [str(executable), entry["operation"], entry["format"], str(input_path)]
        start = time.monotonic()
        preexec_fn = None
        if resource is not None and hasattr(resource, "RLIMIT_AS"):
            def limit_address_space() -> None:
                resource.setrlimit(
                    resource.RLIMIT_AS,
                    (max_address_space_bytes, max_address_space_bytes),
                )

            preexec_fn = limit_address_space
        try:
            completed, elapsed, output_limited = _run_process_bounded(
                command,
                min(max_case_ms, max_total_ms - total_ms) / 1000,
                max_output_bytes,
                preexec_fn,
            )
            elapsed = (time.monotonic() - start) * 1000
            output_bytes = len(completed.stdout) + len(completed.stderr)
            status = "passed"
            if output_limited:
                status = "failed"
                failures.append(f"{entry['id']}: output budget")
            if completed.returncode < 0:
                status = "failed"
                failures.append(f"{entry['id']}: process signal")
        except (subprocess.TimeoutExpired, OSError, ValueError) as error:
            elapsed = (time.monotonic() - start) * 1000
            output_bytes = 0
            status = "failed"
            failures.append(f"{entry['id']}: {type(error).__name__}")
        total_ms += elapsed
        cases.append(
            {
                "case_id": entry["id"],
                "elapsed_ms": round(elapsed, 3),
                "output_bytes": output_bytes,
                "status": status,
            }
        )
    if total_ms > max_total_ms:
        failures.append("total time budget")
    result = {
        "$schema": report_schema(output_dir, "budget-result.schema.json"),
        "schema_version": 1,
        "profile_id": PROFILE_ID,
        "provenance": {**source_binding(), "subject_binary_sha256": sha256_file(executable)},
        "budgets": {
            "max_case_ms": max_case_ms,
            "max_total_ms": max_total_ms,
            "max_output_bytes": max_output_bytes,
            "max_input_bytes": max_input_bytes,
            "max_address_space_bytes": max_address_space_bytes,
        },
        "summary": {
            "status": "passed" if not failures else "failed",
            "cases": len(cases),
            "total_ms": round(total_ms, 3),
            "failures": failures,
            "memory_enforcement": (
                "POSIX RLIMIT_AS"
                if resource is not None and hasattr(resource, "RLIMIT_AS")
                else "unavailable on this platform; decoder ResourceLimits remain active"
            ),
        },
        "cases": cases,
    }
    write_json(report_path(output_dir, "budget-results.json"), result)
    return result
