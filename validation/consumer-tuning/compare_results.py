#!/usr/bin/env python3
"""Verify source-bound controls and compare exact outcomes across native hosts."""

import argparse
import json
from pathlib import Path


def compare(left, right):
    results = [left.resolve(), right.resolve()]
    for result in results:
        if not (result / "COMPLETE").exists():
            raise ValueError(f"incomplete native result: {result}")
    metadata = [json.loads((result / "metadata.json").read_text()) for result in results]
    if {entry["machine"] for entry in metadata} != {"x86_64", "aarch64"}:
        raise ValueError("expected observed native x86_64 and aarch64 results")
    for key in ["lockfile_sha256", "manifest_sha256", "configs", "pairs", "build_rounds",
                "iterations_per_process"]:
        if metadata[0][key] != metadata[1][key]:
            raise ValueError(f"unmatched native experiment controls: {key}")
    if metadata[0]["source_commit"]["stdout"].strip() != metadata[1]["source_commit"]["stdout"].strip():
        raise ValueError("unmatched measurement harness commits")
    manifests = [(result / "fixture-manifest.json").read_bytes() for result in results]
    if manifests[0] != manifests[1]:
        raise ValueError("native hosts did not consume the same canonical manifest")
    outcomes = [json.loads((result / "outcomes.json").read_text()) for result in results]
    if outcomes[0].keys() != outcomes[1].keys():
        raise ValueError("native hosts did not report the same fixtures")
    comparisons = {}
    for backend in ["current", "release022", "hayro-scalar"]:
        differences = {}
        for fixture in outcomes[0]:
            for config in metadata[0]["configs"]:
                values = [entry[fixture]["by_configuration"][backend][config] for entry in outcomes]
                if values[0] != values[1]:
                    differences[f"{fixture}/{config}"] = {
                        metadata[0]["machine"]: values[0], metadata[1]["machine"]: values[1]}
        comparisons[backend] = {"fixtures": len(outcomes[0]),
                                "configurations": len(metadata[0]["configs"]),
                                "exact_cross_architecture_outcome_match": not differences,
                                "differences": differences}
    if comparisons["current"]["differences"] or comparisons["release022"]["differences"]:
        raise ValueError(f"native control output mismatch: {comparisons}")
    return {
        "schema": 1,
        "run_ids": [entry["environment_allowlist"].get("GITHUB_RUN_ID") for entry in metadata],
        "measurement_commits": [entry["source_commit"]["stdout"].strip() for entry in metadata],
        "manifest_sha256": metadata[0]["manifest_sha256"],
        "backends": comparisons, "hayro_is_pixel_oracle": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("left", type=Path)
    parser.add_argument("right", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    options = parser.parse_args()
    report = compare(options.left, options.right)
    options.output.parent.mkdir(parents=True, exist_ok=True)
    options.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
