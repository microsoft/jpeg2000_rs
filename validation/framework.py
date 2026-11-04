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
) -> re.Match[str] | None:
    """Resolve formatted methods in their actual impl, never another short name."""
    short = symbol.rsplit("::", 1)[-1]
    pattern = re.compile(
        rf"(?m)^([ \t]*)(?:(?:pub(?:\([^)\n]*\))?|const|async|unsafe)[ \t]+)*"
        rf"fn[ \t]+{re.escape(short)}\b",
    )
    if "::" in symbol:
        owner = symbol.rsplit("::", 1)[0].rsplit("::", 1)[-1]
        trait_scope = (
            r"(?:Tier1SymbolDecoder[ \t]+for[ \t]+)?"
            if symbol == "RawBitReader::decode" else ""
        )
        if short == "clone":
            trait_scope = r"(?:Clone[ \t]+for[ \t]+)?"
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


def _coverage_same_file_call(
    text: str, caller: str, callee: str, *, distinct_file: bool = False,
) -> bool:
    """Check another formatted function body, not the callee declaration."""
    same_name = caller.rsplit("::", 1)[-1] == callee
    if same_name and not distinct_file:
        return False
    body = _coverage_function_body(text, _coverage_function_header(text, caller))
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
}

_CODING_STYLE_BYTES_CONTRACTS = {
    ("src/codestream/coding_markers.rs", "Parser::parse_cod"): (
        "part1_parse_cod_payload", _coverage_call("parsed_coding_style_outcome", r"\1"), None,
        r"segment\.offset\s*,\s*segment\.payload\s*@\s*,\s*self\.limits",
    ),
    ("src/codestream/coding_markers.rs", "Parser::parse_cod_payload"): (
        "part1_parse_cod_payload", _coverage_call("parsed_coding_style_outcome", r"\1"), None,
        r"segment_offset\s*,\s*payload\s*@\s*,\s*self\.limits",
    ),
}

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
        r"layout\s*,\s*" + _coverage_call("crate::image::decoded_image_view", "decoded") + r"\s*,\s*limits",
    ),
    ("src/decode/api.rs", "decode_typed_layout"): (
        "part2_decode_typed_layout", _coverage_call("crate::image::decoded_typed_image_outcome", r"\1"), None,
        r"input_bytes\s*,\s*layout\s*,\s*limits\s*,\s*requested",
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
    ("src/codestream/extensions.rs", "Part2Extensions::nonlinear_transform_for"): (
        "part2_nonlinear_transform_for", _coverage_call("nonlinear_transform_option_view", r"\1"), None,
        _coverage_call("owned_extensions_view", "self") + r"\.nonlinear\s*,\s*component",
    ),
    ("src/decode/api.rs", "nonlinear_component_extent"): (
        "part2_nonlinear_component_extent", r"\1", None,
        r"size\s*,\s*" + _coverage_call("crate::image::typed_image_value_view", r"\*\s*image") + r"\s*,\s*component",
    ),
    ("src/decode/api.rs", "collect_nonlinear_regions"): (
        "part2_collect_nonlinear_regions", _coverage_call("nonlinear_regions_outcome", r"\1"), None,
        r"layout\s*,\s*" + _coverage_call("crate::image::typed_image_value_view", r"\*\s*image"),
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
            )
        return headers[key]

    def cross_file_call(
        path: Path, caller: str, callee: str, *, require_caller_body: bool,
    ) -> bool:
        if require_caller_body:
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
        prefix = r"(?<![\w.])" if same_name else r"\b"
        return body is not None and re.search(rf"{prefix}{re.escape(callee)}\s*\(", body) is not None

    ids: set[str] = set()
    contract_functions: set[tuple[str, str]] = set()
    for entry in coverage["requirements"]:
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
            if (reference["path"], reference["symbol"]) in (
                _PACKET_PROVED_BOUNDARY_APIS | _RECONSTRUCTION_PROVED_BOUNDARY_APIS
                | _RESOLUTION_GEOMETRY_PROVED_BOUNDARY_APIS
                | _SUBBAND_ADMISSION_PROVED_BOUNDARY_APIS
                | _SUBBAND_VECTOR_PROVED_BOUNDARY_APIS
            )
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
                    r"output@\s*,\s*target\s*,\s*" + kernel_step_view + r"\s*,\s*" + kernel_view,
                ),
                ("src/transform/arbitrary.rs", "arbitrary_irreversible_target"): (
                    None, "part2_atk_irreversible_target",
                    r"output@\s*,\s*target\s*,\s*" + kernel_step_view + r"\s*,\s*" + kernel_view,
                ),
                ("src/transform/arbitrary.rs", "lifting_source_sum"): (
                    None, "part2_atk_source_sum",
                    r"samples@\s*,\s*target\s*,\s*coefficient\s*,\s*offset\s*,\s*whole_sample_filter\s*,\s*whole_sample_extension",
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
                or _CODESTREAM_READER_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _SOT_READER_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TILE_DATA_WINDOW_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _SIZ_GEOMETRY_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _LAYOUT_PROLOGUE_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _MAIN_HEADER_ADMISSION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TILE_HEADER_ADMISSION_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _RAW_TILE_HEADER_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _ROI_SETTER_CONTRACTS.get((reference["path"], reference["symbol"]))
                or _TILE_PART_READER_CONTRACTS.get((reference["path"], reference["symbol"]))
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
                or (re.search(r"\brequires\b", contract) is None
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
            if claimed_consumer and not any(
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
