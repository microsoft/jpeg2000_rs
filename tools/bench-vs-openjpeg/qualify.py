#!/usr/bin/env python3
"""Inventory every decoder outcome before timing; refusals/crashes never become speedups."""

import argparse
import json
import os
from pathlib import Path
import sys

from run import capture, check_source, compare_dumps, load_corpus, sha, write_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--rust", type=Path, required=True)
    parser.add_argument("--openjpeg", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--qualified-manifest", type=Path, required=True)
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument("--reduce", type=int, default=0)
    parser.add_argument("--window", default="-")
    parser.add_argument("--maximum-address-space", type=int, default=8 * 1024**3)
    options = parser.parse_args()
    if options.cpu not in os.sched_getaffinity(0) or not 0 <= options.reduce <= 16:
        parser.error("invalid CPU or reduction")
    if options.maximum_address_space < 0:
        parser.error("maximum address space must be nonnegative")
    destination = options.qualified_manifest.resolve()
    if destination.exists() or destination.parent != options.manifest.resolve().parent:
        parser.error("qualified manifest must be fresh and beside its source manifest")
    document = load_corpus(options.manifest)
    output = options.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, OPJ_NUM_THREADS="0", BENCH_OPENJPEG_THREADS="1")
    binaries = {"rust": options.rust.resolve(), "openjpeg": options.openjpeg.resolve()}
    records, accepted = [], []
    for case in document["cases"]:
        row = dict(id=case["id"], corpus_class=case["corpus_class"], input_sha256=case["sha256"],
                   processes={})
        dumps = {}
        for backend, binary in binaries.items():
            data, metrics = capture(
                ["taskset", "-c", options.cpu, binary, case["path"], "dump",
                 options.reduce, options.window, "1", "0", "0"],
                output / case["id"] / backend, env,
                maximum_address_space=options.maximum_address_space)
            row["processes"][backend] = metrics
            if metrics["returncode"] == 0:
                dumps[backend] = data
        if len(dumps) != 2:
            row["status"] = "decoder-refusal-or-failure"
        else:
            try:
                row["comparison"] = compare_dumps(dumps["rust"], dumps["openjpeg"])
                if case["lossless"] and row["comparison"]["differing_samples"]:
                    row["status"] = "lossless-mismatch"
                else:
                    if case["lossless"] and options.reduce == 0 and options.window == "-":
                        check_source(dumps["rust"], case)
                    row["status"] = "accepted-with-recorded-numerics"
            except ValueError as error:
                row.update(status="output-validation-failed", error=str(error))
        if row["status"] == "accepted-with-recorded-numerics":
            accepted.append(dict(case, path=str(Path(case["path"]).relative_to(destination.parent))))
        print(case["id"], row["status"], flush=True)
        records.append(row)
    all_passed = len(accepted) == len(records)
    write_json(output / "qualification.json", {
        "scope": "full inventory; accepted subset for timing, not official/normative conformance",
        "source_manifest_sha256": document["source_manifest_sha256"],
        "binary_sha256": {key: sha(path.read_bytes()) for key, path in binaries.items()},
        "request": {"reduce": options.reduce, "window": options.window},
        "maximum_address_space": options.maximum_address_space,
        "total": len(records), "accepted": len(accepted), "all_passed": all_passed,
        "records": records,
    })
    write_json(destination, dict(document, cases=accepted, qualification={
        "total": len(records), "accepted": len(accepted), "all_passed": all_passed,
        "inventory": str(output / "qualification.json"),
        "request": {"reduce": options.reduce, "window": options.window},
        "irreversible": "difference statistics retained, not an independently established tolerance"}))
    print(f"Accepted {len(accepted)}/{len(records)}; every other outcome remains in the inventory")
    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())
