#!/usr/bin/env python3
"""Inventory every decoder outcome before timing; refusals/crashes never become speedups."""

import argparse
import json
import os
from pathlib import Path
import re
import sys
import struct
from array import array

from run import capture, check_source, compare_dumps, load_corpus, read_dump, sha, write_json
from corpus import coding_header


def crop_dump(data, window):
    shape, planes = read_dump(data)
    x, y, width, height = window
    if min(x, y) < 0 or min(width, height) <= 0 or x + width > shape[0] or y + height > shape[1]:
        raise ValueError("crop falls outside full image")
    output = [struct.pack("<3Q", width, height, len(planes))]
    for (w, h, precision, signed), values in planes:
        if (w, h) != shape:
            raise ValueError("crop oracle requires unit-sampled components")
        cropped = array(values.typecode)
        for row in range(y, y + height):
            cropped.extend(values[row * w + x:row * w + x + width])
        if sys.byteorder != "little":
            cropped.byteswap()
        output.extend([struct.pack("<4Q", width, height, precision, signed), cropped.tobytes()])
    return b"".join(output)


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
    parser.add_argument("--case", default=".")
    parser.add_argument("--check-window-crop", action="store_true",
                        help="also compare each window with its own full decode (zero-origin unit sampling)")
    parser.add_argument("--maximum-address-space", type=int, default=8 * 1024**3)
    options = parser.parse_args()
    if options.cpu not in os.sched_getaffinity(0) or not 0 <= options.reduce <= 16:
        parser.error("invalid CPU or reduction")
    if options.maximum_address_space < 0:
        parser.error("maximum address space must be nonnegative")
    window = None
    if options.check_window_crop:
        try:
            window = tuple(map(int, options.window.split(",")))
        except ValueError:
            parser.error("crop checking requires x,y,width,height")
        if len(window) != 4 or options.reduce != 0:
            parser.error("crop checking requires four window coordinates and no reduction")
    destination = options.qualified_manifest.resolve()
    if destination.exists() or destination.parent != options.manifest.resolve().parent:
        parser.error("qualified manifest must be fresh and beside its source manifest")
    document = load_corpus(options.manifest)
    cases = [case for case in document["cases"] if re.search(options.case, case["id"])]
    if not cases:
        parser.error("case selector matched no inputs")
    output = options.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, OPJ_NUM_THREADS="0", BENCH_OPENJPEG_THREADS="1")
    binaries = {"rust": options.rust.resolve(), "openjpeg": options.openjpeg.resolve()}
    records, accepted = [], []
    for case in cases:
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
                    if options.check_window_crop:
                        if coding_header(Path(case["path"]).read_bytes())["origin"] != [0, 0]:
                            raise ValueError("crop oracle requires zero image origin")
                        row["own_full_crop"] = {}
                        for backend, binary in binaries.items():
                            full, metrics = capture(
                                ["taskset", "-c", options.cpu, binary, case["path"],
                                 "dump", "0", "-", "1", "0", "0"],
                                output / case["id"] / (backend + "-full-dump"), env,
                                maximum_address_space=options.maximum_address_space)
                            row["processes"][backend + "-full"] = metrics
                            if metrics["returncode"] != 0:
                                row["status"] = "full-crop-decoder-refusal-or-failure"
                                continue
                            if case["lossless"]:
                                check_source(full, case)
                            comparison = compare_dumps(dumps[backend], crop_dump(full, window))
                            comparison["window_sha256"] = comparison.pop("rust_sha256")
                            comparison["full_crop_sha256"] = comparison.pop("openjpeg_sha256")
                            row["own_full_crop"][backend] = comparison
                            if comparison["differing_samples"]:
                                row["status"] = "own-full-crop-mismatch"
                            del full
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
        "qualifier_sha256": sha(Path(__file__).read_bytes()),
        "binary_sha256": {key: sha(path.read_bytes()) for key, path in binaries.items()},
        "request": {"reduce": options.reduce, "window": options.window},
        "case_selector": options.case,
        "own_full_crop_checked": options.check_window_crop,
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
