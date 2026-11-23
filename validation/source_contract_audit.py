#!/usr/bin/env python3
"""Triage captured compiler origins/contracts; never infer functional coverage."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
from typing import Any

from framework import validate_schema, write_json


VALIDATION = Path(__file__).resolve().parent
VERUS_COMMIT = "426d8b01e7ffb910a36c15e1f870ff985bb61eef"


def _digest(value: dict[str, Any]) -> str:
    return hashlib.sha256(
        (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()
    ).hexdigest()


def _canonical(value: dict[str, Any]) -> tuple[str, str]:
    if not isinstance(value, dict) or not isinstance(value.get("path"), dict):
        raise ValueError("invalid canonical compiler identity")
    path = value["path"]
    if set(value) != {"path"} or set(path) != {"krate", "segments"}:
        raise ValueError("unexpected canonical compiler identity shape")
    crate = path["krate"]
    if isinstance(crate, dict):
        if set(crate) != {"Id"} or len(crate["Id"]) != 2:
            raise ValueError("invalid canonical crate identity")
        name, stable_id = crate["Id"]
        if type(stable_id) is not int or not 0 <= stable_id < 2**64:
            raise ValueError("invalid canonical stable crate ID")
    elif crate in ("Core", "Alloc", "Vstd", "Internal"):
        name = {"Core": "core", "Alloc": "alloc", "Vstd": "vstd", "Internal": "builtin"}[crate]
    else:
        raise ValueError("unknown canonical crate identity")
    if not isinstance(path["segments"], list) or not path["segments"]:
        raise ValueError("invalid canonical compiler path segments")
    segments = [name, *path["segments"]]
    if not all(isinstance(part, str) and part and "::" not in part for part in segments):
        raise ValueError("invalid canonical compiler path segment")
    return json.dumps(value, sort_keys=True, separators=(",", ":")), "::".join(segments)


def _compiler_crosswalk(
    inventory: dict[str, Any], proof: dict[str, Any],
    capture: dict[str, Any], binding: dict[str, Any],
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    provenance = inventory["provenance"]
    if (binding["before"] != provenance or binding["after"] != provenance
            or binding["workflow_flags"] != proof["verus"]["workflow_flags"]
            or binding["artifact_sha256"] != {
                "inventory": _digest(inventory), "proof": _digest(proof),
                "compiler_identities": _digest(capture),
            }):
        raise ValueError("compiler identity capture has different source/profile or artifact binding")
    if (type(capture["format_version"]) is not int or capture["format_version"] != 1
            or capture["cargo_mode"] is not True
            or capture["entire_crate"] is not True or type(capture["errors"]) is not int
            or capture["errors"] != 0 or type(capture["verified"]) is not int
            or capture["verified"] != proof["results"]["verus_verified_obligations"]
            or capture["compiler_version"]["verus"]["commit"] != VERUS_COMMIT
            or any(capture[field] != "not-measured" for field in (
                "source_function_coverage", "functional_coverage", "runtime_reachability"))):
        raise ValueError("unqualified compiler identity capture or verification profile")
    definitions = {}
    project_crates = set()
    for row in capture["functions"]:
        identity, symbol = _canonical(row["canonical"])
        if identity in definitions:
            raise ValueError("duplicate canonical compiler definition")
        if row["mode"] not in ("Exec", "Spec", "Proof"):
            raise ValueError("unknown canonical function mode")
        if symbol.startswith("jpeg2000_decoder::"):
            project_crates.add(row["canonical"]["path"]["krate"]["Id"][1])
        definitions[identity] = (symbol, row)
    if len(project_crates) != 1:
        raise ValueError("missing or mixed canonical project crate IDs")
    results = {}
    labels: dict[str, list[str]] = {}
    for row in capture["result_identities"]:
        identity, symbol = _canonical(row["canonical"])
        if (symbol.startswith("jpeg2000_decoder::")
                and row["canonical"]["path"]["krate"]["Id"][1] not in project_crates):
            raise ValueError("canonical result uses a different project crate ID")
        if identity in results:
            raise ValueError("duplicate canonical compiler result")
        if not isinstance(row["result_details"], dict):
            raise ValueError("missing canonical result details")
        results[identity] = row
        labels.setdefault(row["compiler_result_label"], []).append(identity)
    for label, identities in labels.items():
        expected = "unique-reported-label" if len(identities) == 1 else "shared-reported-label"
        for identity in identities:
            row = results[identity]
            if (row["reported_label_canonical_count"] != len(identities)
                    or row["reported_label_disposition"] != expected):
                raise ValueError("inconsistent compiler result label multiplicity")
    projected_labels = {row["function"] for row in proof["functions"]}
    if {label for label in labels if label.startswith("jpeg2000_decoder::")} != projected_labels:
        raise ValueError("canonical result labels differ from the bound proof report")
    by_symbol = {}
    for identity, (symbol, row) in definitions.items():
        if not symbol.startswith("jpeg2000_decoder::"):
            continue
        if symbol in by_symbol:
            raise ValueError("ambiguous canonical project symbol")
        result = results.get(identity)
        if result is not None and (
                result["mode"] != row["mode"]
                or result["compiler_result_label"] != row["compiler_result_label"]
                or result["result_details"] != row["result_details"]):
            raise ValueError("canonical definition/result records disagree")
        by_symbol[symbol] = {
            "mode": row["mode"],
            "compiler_result_label": row["compiler_result_label"],
            "compiler_result_identity": (
                "canonical-result-present-shared-label" if result is not None
                and result["reported_label_canonical_count"] > 1 else
                "canonical-result-present" if result is not None else "no-canonical-result-record"
            ),
        }
    return by_symbol, {
        "canonical_result_identities": len(results),
        "reported_result_labels": len(labels),
        "shared_reported_labels": {
            label: len(identities) for label, identities in labels.items() if len(identities) > 1
        },
        "binding": binding,
        "scope": "Compiler identity correspondence, not a production denominator or functional proof.",
    }


def _index(rows: list[dict[str, Any]], key: str) -> dict[str, dict[str, Any]]:
    result = {row[key]: row for row in rows}
    if len(result) != len(rows):
        raise ValueError(f"duplicate {key} in captured observations")
    return result


def _postcondition(function: dict[str, Any]) -> str:
    if function["body_disposition"] == "bodyless-trait-declaration":
        return "abstract-declaration"
    if any(function["ensure_counts"]) or function["returns_expression"]:
        return "explicit-postcondition-present-unreviewed"
    return "no-explicit-postcondition"


def audit(
    inventory: dict[str, Any], proof: dict[str, Any],
    compiler_identities: dict[str, Any] | None = None,
    identity_binding: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Audit historical artifacts, not the current checkout or fresh compilation."""
    validate_schema(VALIDATION / "source-inventory.schema.json", inventory)
    validate_schema(VALIDATION / "proof-coverage.schema.json", proof)
    if inventory["provenance"] != proof["provenance"]:
        raise ValueError("inventory and verifier source/tool provenance differ")
    if inventory["provenance"]["git_dirty"]:
        raise ValueError("compiler capture must identify clean source")
    if inventory["lifetime_analysis"] != proof["known_proof_boundary"]["lifetime_analysis"]:
        raise ValueError("inventory and verifier lifetime boundaries differ")
    hashes = inventory["provenance"]["source_hashes"]
    if any(hashes.get(path) != digest for path, digest in proof["source_hashes"].items()):
        raise ValueError("proof source hashes differ from capture provenance")
    native = _index(inventory["native_functions"], "source_id")
    vir = _index(inventory["vir_functions"], "symbol")
    results = _index(proof["functions"], "function")
    if len(results) != proof["results"]["verified_project_functions"]:
        raise ValueError("verifier result count differs from its identity list")
    if len(native) != inventory["counts"]["native_function_items"]:
        raise ValueError("native item count differs from its identity list")
    for symbol, function in vir.items():
        if function["native_origin_disposition"] == "same-source-declaration-and-body-extent":
            source = native.get(function["native_source_ids"][0])
            if (source is None
                    or source["origin_disposition"] != "same-source-declaration-and-body-extent"
                    or source["vir_candidates"] != [symbol]):
                raise ValueError("VIR/native origin association is not reciprocal")

    native_rows = []
    for source_id, function in sorted(native.items()):
        if any(symbol not in vir for symbol in function["vir_candidates"]):
            raise ValueError("native candidate refers to an absent VIR identity")
        symbol = None
        syntax = "unresolved-native-to-vir"
        observation = "unresolved-native-to-vir"
        if function["origin_disposition"] == "same-source-declaration-and-body-extent":
            candidates = function["vir_candidates"]
            if len(candidates) != 1:
                raise ValueError("exact native origin does not have one VIR identity")
            symbol = candidates[0]
            matched = vir[symbol]
            if (matched["mode"] != "Exec"
                    or matched["native_origin_disposition"] != "same-source-declaration-and-body-extent"
                    or matched["native_source_ids"] != [source_id]):
                raise ValueError("native/VIR origin association is not reciprocal")
            syntax = _postcondition(matched)
            observation = ("exact-result-key-present" if symbol in results
                           else "result-key-crosswalk-unresolved")
        native_rows.append({
            "source_id": source_id, "path": function["path"],
            "begin": function["begin"], "end": function["end"], "name": function["name"],
            "origin_disposition": function["origin_disposition"],
            "vir_symbol": symbol, "postcondition_syntax": syntax,
            "whole_crate_result_identity": observation,
            "functional_contract_review": "not-reviewed",
            "runtime_reachability": "not-measured",
        })

    exec_rows = [{
        "symbol": symbol, "span": function["span"],
        "native_origin_disposition": function["native_origin_disposition"],
        "native_source_ids": function["native_source_ids"],
        "postcondition_syntax": _postcondition(function),
        "contract_sha256": function["contract_sha256"],
        "whole_crate_result_identity": (
            "exact-result-key-present" if symbol in results else "result-key-crosswalk-unresolved"),
        "functional_contract_review": "not-reviewed",
        "runtime_reachability": "not-measured",
    } for symbol, function in sorted(vir.items()) if function["mode"] == "Exec"]
    report = {
        "report_kind": "source-contract-triage-v1",
        "capture_provenance": inventory["provenance"],
        "compiler_capture": inventory["compiler_capture"],
        "compiler_input_sha256": inventory["input_sha256"],
        "source_function_coverage": "not-measured",
        "functional_coverage": "not-measured",
        "runtime_reachability": "not-measured",
        "lifetime_analysis": proof["known_proof_boundary"]["lifetime_analysis"],
        "counts": {
            "native_items": len(native_rows),
            "native_postcondition_syntax": dict(Counter(
                row["postcondition_syntax"] for row in native_rows)),
            "exec_postcondition_syntax": dict(Counter(
                row["postcondition_syntax"] for row in exec_rows)),
            "exec_result_identity": dict(Counter(
                row["whole_crate_result_identity"] for row in exec_rows)),
            "all_modes_exact_result_keys": len(vir.keys() & results.keys()),
            "all_modes_vir_keys_without_exact_result_key": len(vir.keys() - results.keys()),
            "result_keys_without_exact_vir_key": len(results.keys() - vir.keys()),
        },
        "native_items": native_rows,
        "verus_exec_items": exec_rows,
        "result_keys_without_exact_vir_key": sorted(results.keys() - vir.keys()),
        "boundaries": [
            "Offline artifact triage is not fresh compilation or independent capture qualification.",
            "Rustdoc origins do not establish a complete native production denominator.",
            "Only exact VIR/result key equality is joined; impl/display-name crosswalks remain unresolved.",
            "A result key is an observation, not proof of a complete functional contract or a per-item query.",
            "Postcondition presence cannot distinguish full functional from safety/shape-only contracts.",
            "No explicit postcondition does not mean no precondition, termination check, or body verification.",
            "Source-origin association is not native/Verus erasure equivalence.",
            "The Verus dependency graph is not a native runtime call graph; no public/private reachability is inferred.",
        ],
    }
    if (compiler_identities is None) != (identity_binding is None):
        raise ValueError("compiler identities and their binding must be supplied together")
    if compiler_identities is not None and identity_binding is not None:
        crosswalk, summary = _compiler_crosswalk(inventory, proof, compiler_identities, identity_binding)
        for row in exec_rows:
            observed = crosswalk.get(row["symbol"])
            if observed is not None and observed["mode"] != "Exec":
                raise ValueError("compiler identity mode differs from the VIR observation")
            row["compiler_result_identity"] = (
                observed["compiler_result_identity"] if observed is not None
                else "canonical-definition-not-captured"
            )
            row["compiler_result_label"] = observed["compiler_result_label"] if observed else None
        report["report_kind"] = "source-contract-triage-v2"
        report["compiler_result_crosswalk"] = summary
        report["counts"]["exec_compiler_result_identity"] = dict(Counter(
            row["compiler_result_identity"] for row in exec_rows
        ))
        report["boundaries"][2] = (
            "Compiler canonical identities supply the optional result crosswalk; shared reported labels "
            "are retained, not counted as unique source-function proofs."
        )
        report["boundaries"].append(
            "The supplied compiler binding is checked for consistency, not independently authenticated."
        )
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--compiler-identities", type=Path)
    parser.add_argument("--identity-binding", type=Path)
    args = parser.parse_args()
    try:
        inventory_bytes = args.inventory.read_bytes()
        proof_bytes = args.proof.read_bytes()
        identity_bytes = args.compiler_identities.read_bytes() if args.compiler_identities else None
        binding_bytes = args.identity_binding.read_bytes() if args.identity_binding else None
        report = audit(
            json.loads(inventory_bytes), json.loads(proof_bytes),
            json.loads(identity_bytes) if identity_bytes is not None else None,
            json.loads(binding_bytes) if binding_bytes is not None else None,
        )
        report["artifact_sha256"] = {
            "inventory": hashlib.sha256(inventory_bytes).hexdigest(),
            "proof": hashlib.sha256(proof_bytes).hexdigest(),
            "audit_tool": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        }
        if identity_bytes is not None and binding_bytes is not None:
            report["artifact_sha256"].update({
                "compiler_identities": hashlib.sha256(identity_bytes).hexdigest(),
                "identity_binding": hashlib.sha256(binding_bytes).hexdigest(),
            })
        write_json(args.output, report)
    except (ValueError, KeyError, TypeError, OSError) as error:
        parser.exit(2, f"source contract audit rejected: {error}\n")
    print(json.dumps({"status": "observations-only", "counts": report["counts"]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
