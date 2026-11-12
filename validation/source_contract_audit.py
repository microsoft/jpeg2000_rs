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


def audit(inventory: dict[str, Any], proof: dict[str, Any]) -> dict[str, Any]:
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
    return {
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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        inventory_bytes = args.inventory.read_bytes()
        proof_bytes = args.proof.read_bytes()
        report = audit(json.loads(inventory_bytes), json.loads(proof_bytes))
        report["artifact_sha256"] = {
            "inventory": hashlib.sha256(inventory_bytes).hexdigest(),
            "proof": hashlib.sha256(proof_bytes).hexdigest(),
            "audit_tool": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        }
        write_json(args.output, report)
    except (ValueError, KeyError, TypeError, OSError) as error:
        parser.exit(2, f"source contract audit rejected: {error}\n")
    print(json.dumps({"status": "observations-only", "counts": report["counts"]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
