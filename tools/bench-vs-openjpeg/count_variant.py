#!/usr/bin/env python3
"""Collect separate paired whole-process hardware counters for an isolated variant."""

import argparse
import json
import os
from pathlib import Path
import re

from run import execute, sha, write_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--comparison", type=Path, required=True)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--perf", default="perf")
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument("--case", default="^(day-small-gray-lossless|day-small-gray-lossy-r40|style-b32-m0|structure-tile256)$")
    options = parser.parse_args()
    comparison, baseline = options.comparison.resolve(), options.baseline.resolve()
    if not (comparison / "COMPLETE.json").is_file() or not (baseline / "COMPLETE.json").is_file():
        parser.error("requires completed comparison and control")
    if options.cpu not in os.sched_getaffinity(0):
        parser.error("CPU is outside allowed affinity")
    output = options.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    cases = [case for case in json.loads((baseline / "corpus.json").read_text())["cases"]
             if re.search(options.case, case["id"])]
    if not cases:
        parser.error("no matching counter cases")
    for case in cases:
        if sha(Path(case["path"]).read_bytes()) != case["sha256"]:
            raise ValueError(f"input bytes changed: {case['id']}")
    env = dict(os.environ, OPJ_NUM_THREADS="0", BENCH_OPENJPEG_THREADS="1", LC_ALL="C")
    records = []
    for binding in sorted(comparison.glob("*/binaries.json")):
        config = binding.parent.name
        identities = json.loads(binding.read_text())
        binaries = {
            "baseline": baseline / config / "cargo/release/bench-vs-openjpeg",
            "candidate": comparison / config / "cargo/release/bench-vs-openjpeg",
        }
        for backend, binary in binaries.items():
            if sha(binary.read_bytes()) != identities[backend]:
                raise ValueError(f"counter binary hash changed: {config}/{backend}")
        for case in cases:
            for repeat in range(3):
                order = ["baseline", "candidate"] if repeat % 2 == 0 else ["candidate", "baseline"]
                for backend in order:
                    prefix = output / config / case["id"] / f"{backend}-{repeat}"
                    prefix.parent.mkdir(parents=True, exist_ok=True)
                    counter = prefix.parent / f"{prefix.name}-counters.csv"
                    execute(
                        [options.perf, "stat", "-x", ";", "-o", counter, "-e",
                         "cycles:u,instructions:u,branches:u,branch-misses:u,L1-dcache-load-misses:u,LLC-load-misses:u",
                         "--", "taskset", "-c", options.cpu, binaries[backend], case["path"],
                         "typed", "0", "-", "1", "0", "0"], prefix, env,
                        maximum_address_space=8 * 1024**3)
                    records.append(dict(config=config, case=case["id"], backend=backend,
                                        repeat=repeat, binary_sha256=identities[backend],
                                        input_sha256=case["sha256"], counter_file=str(counter.relative_to(output))))
    if not records:
        raise ValueError("comparison has no bound executable configurations")
    write_json(output / "COMPLETE.json", dict(
        scope="Separate whole-process user-space counters, startup/input/one decode/drop included; not timed-stage counts",
        comparison_provenance=json.loads((comparison / "provenance.json").read_text()),
        records=records, unsupported="Keep literal unsupported markers; never zero-fill",
        collector_sha256=sha(Path(__file__).read_bytes())))


if __name__ == "__main__":
    main()
