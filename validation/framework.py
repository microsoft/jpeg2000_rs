#!/usr/bin/env python3
"""Reproducible decoder validation without publication approval state."""

from __future__ import annotations

import hashlib
import json
import math
import os
import re
import selectors
import shutil
import struct
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
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


def validate_schema(schema_path: Path, value: Any) -> None:
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    Draft202012Validator.check_schema(schema)
    try:
        Draft202012Validator(schema, format_checker=FORMAT_CHECKER).validate(value)
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
        ("hayro-comparison.json", "hayro-comparison.schema.json"),
    ):
        path = (output_dir or RESULTS_DIR) / name
        if path.is_file():
            validate_schema(VALIDATION / schema, json.loads(path.read_text()))
            reports.append(name)
    return {"status": "passed", "schemas": checked, "reports": reports}


def _coverage_symbol_present(path: Path, symbol: str) -> bool:
    short = re.escape(symbol.rsplit("::", 1)[-1])
    return bool(re.search(
        rf"\b(?:fn|struct|enum|type|const|trait)\s+{short}\b",
        path.read_text(encoding="utf-8"),
    ))


def validate_normative_coverage(
    coverage: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Check the links present, without asserting exhaustive clause coverage."""
    if coverage is None:
        coverage = json.loads((ROOT / "normative-coverage.json").read_text())
    validate_schema(ROOT / "normative-coverage.schema.json", coverage)
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
                if not _coverage_symbol_present(path, reference["symbol"]):
                    raise ValueError(
                        f"missing normative evidence symbol: {reference['path']}::{reference['symbol']}"
                    )
        spec_symbols = {reference["symbol"] for reference in entry["spec_refs"]}
        for reference in entry["contract_refs"]:
            text = (ROOT / reference["path"]).read_text(encoding="utf-8")
            short = reference["symbol"].rsplit("::", 1)[-1]
            signature_match = re.search(rf"\bfn\s+{re.escape(short)}\b", text)
            if signature_match is None:
                raise ValueError(f"missing linked contract function: {short}")
            signature = signature_match.start()
            contract_start = text.rfind("#[cfg_attr", 0, signature)
            contract = text[contract_start:signature] if contract_start >= 0 else ""
            if "verus_spec(" not in contract or "ensures returns" not in contract:
                raise ValueError(f"linked function lacks executable Verus contract: {short}")
            if not any(re.search(rf"\b{re.escape(symbol)}\b", contract) for symbol in spec_symbols):
                raise ValueError(f"linked function contract lacks normative spec reference: {short}")
            if not any(
                re.search(rf"\b{re.escape(short)}\s*\(", (ROOT / ref["path"]).read_text())
                for ref in entry["implementation_refs"]
                if ref["path"] != reference["path"]
            ):
                raise ValueError(f"linked function is not used by claimed implementation: {short}")
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
) -> bytes:
    if width <= 0 or height <= 0 or components not in (1, 3) or not 1 <= precision <= 38:
        raise ValueError("generated container requires positive geometry and uniform unsigned grayscale/RGB components")
    signature = box(b"jP  ", b"\x0d\x0a\x87\x0a")
    ftyp = box(b"ftyp", brand + b"\0\0\0\0" + brand)
    ihdr = box(b"ihdr", struct.pack(">IIH4B", height, width, components, precision - 1, 7, 0, 0))
    colr = box(b"colr", bytes((1, 0, 0, 0, 0, 0, 17 if components == 1 else 16)))
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


def _run_process_bounded(
    command: list[str],
    timeout_seconds: float,
    max_output_bytes: int,
    preexec_fn: Any,
) -> tuple[subprocess.CompletedProcess[bytes], float, bool]:
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
