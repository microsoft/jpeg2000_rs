#!/usr/bin/env python3
"""Count whole-process instructions separately from uninstrumented timing."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess

from run import capture, sha, write_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cpu", type=int, required=True)
    parser.add_argument("--case", default="^(day-small-gray-lossless|day-small-gray-lossy-r40|style-b32-m0|structure-untiled)$")
    options = parser.parse_args()
    baseline = options.baseline.resolve()
    if not (baseline / "COMPLETE.json").is_file():
        parser.error("requires a completed, hash-bound build matrix")
    options.output.mkdir(parents=True, exist_ok=False)
    valgrind = os.environ.get("VALGRIND", "valgrind")
    write_json(options.output / "scope.json", dict(
        scope="Whole process: startup, input, one decode, conversion and destruction; not stage counts",
        valgrind=subprocess.check_output([valgrind, "--version"], text=True).strip(),
        architecture=os.uname().machine, cpu=options.cpu))
    corpus = json.loads((baseline / "corpus.json").read_text())
    cases = [case for case in corpus["cases"] if re.search(options.case, case["id"])]
    if not cases:
        parser.error("instruction case selector matched no measured inputs")
    for case in cases:
        if sha(Path(case["path"]).read_bytes()) != case["sha256"]:
            raise ValueError(f"input hash differs: {case['id']}")
    outcomes = []
    builds = sorted(baseline.glob("*/build.json"))
    if not builds:
        raise ValueError("completed matrix has no bound builds")
    for build in builds:
        config = build.parent.name
        metadata = json.loads(build.read_text())
        binaries = {
            "rust": (build.parent / "cargo/release/bench-vs-openjpeg", "rust_binary_sha256"),
            "openjpeg": (build.parent / "bench-openjpeg", "c_binary_sha256"),
        }
        for backend, (binary, key) in binaries.items():
            if sha(binary.read_bytes()) != metadata[key]:
                raise ValueError(f"binary hash differs: {config}/{backend}")
            for case in cases:
                prefix = options.output / config / case["id"] / backend
                raw = prefix.parent / f"{prefix.name}.callgrind.out"
                raw.parent.mkdir(parents=True, exist_ok=True)
                _, metrics = capture(
                    ["taskset", "-c", options.cpu, valgrind, "--tool=callgrind",
                     f"--callgrind-out-file={raw}", binary, case["path"],
                     "typed", "0", "-", "1", "0", "0"], prefix,
                    dict(os.environ, OPJ_NUM_THREADS="0", BENCH_OPENJPEG_THREADS="1"))
                events = None
                if metrics["returncode"] == 0:
                    events = callgrind_instructions(raw.read_text())
                outcomes.append(dict(config=config, case=case["id"], backend=backend,
                                     binary_sha256=metadata[key], instructions=events,
                                     returncode=metrics["returncode"]))
    write_json(options.output / "outcomes.json", outcomes)
    if any(row["returncode"] != 0 for row in outcomes):
        raise RuntimeError("instruction collection failed; raw refusal/error outcomes retained")


def callgrind_instructions(text):
    lines = text.splitlines()
    events = [line.split()[1:] for line in lines if line.startswith("events:")]
    summaries = [line.split()[1:] for line in lines if line.startswith("summary:")]
    if len(events) != 1 or len(summaries) != 1 or "Ir" not in events[0]:
        raise ValueError("expected exactly one Callgrind instruction event summary")
    value = int(summaries[0][events[0].index("Ir")])
    if value <= 0:
        raise ValueError("instruction count must be positive")
    return value


if __name__ == "__main__":
    main()
