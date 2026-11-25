#!/usr/bin/env python3
"""Pair one isolated prototype with the exact control from run.py; never stack candidates."""

import argparse
import csv
import json
import os
from pathlib import Path
import re
import statistics
import subprocess
import sys

from run import compare_dumps, execute, make_consumer, sha, write_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--candidate-source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--configs", default="generic,consumer")
    parser.add_argument("--case", default=".")
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument("--numerical-299", type=Path)
    options = parser.parse_args()
    baseline = options.baseline.resolve()
    if not (baseline / "COMPLETE.json").exists():
        parser.error("baseline matrix is incomplete")
    if options.cpu not in os.sched_getaffinity(0):
        parser.error("CPU is outside allowed affinity")
    source = options.candidate_source.resolve()
    dirty = subprocess.check_output(["git", "-C", source, "status", "--porcelain"], text=True).strip()
    if dirty:
        parser.error("commit the prototype before measuring")
    output = options.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    consumer = output / "consumer"
    make_consumer(consumer, source)
    cases = [c for c in json.loads((baseline / "corpus.json").read_text())["cases"]
             if re.search(options.case, c["id"])]
    if not cases:
        parser.error("no matching cases")
    provenance = {
        "argv": sys.argv,
        "commit": subprocess.check_output(["git", "-C", source, "rev-parse", "HEAD"], text=True).strip(),
        "source_tree": subprocess.check_output(["git", "-C", source, "rev-parse", "HEAD:src"], text=True).strip(),
        "control": str(baseline), "cpu": options.cpu,
        "method": "three warmups, >=15 iterations AND >=2 seconds; reversed fresh-process pairs",
    }
    write_json(output / "provenance.json", provenance)
    raw_rows, summaries = [], []
    with (output / "raw.csv").open("w") as stream:
        writer = csv.DictWriter(stream, fieldnames=["config", "case", "class", "backend", "round", "sample", "ns"], lineterminator="\n")
        writer.writeheader()
        for config in options.configs.split(","):
            metadata = json.loads((baseline / config / "build.json").read_text())
            env = dict(os.environ, OPJ_NUM_THREADS="0", BENCH_OPENJPEG_THREADS="1",
                       CARGO_TARGET_DIR=str(output / config / "cargo"), CARGO_PROFILE_RELEASE_DEBUG="1")
            env.pop("CARGO_ENCODED_RUSTFLAGS", None)
            for key, value in [
                ("RUSTFLAGS", metadata["rustflags"]),
                ("CARGO_PROFILE_RELEASE_LTO", metadata["lto"]),
                ("CARGO_PROFILE_RELEASE_CODEGEN_UNITS", metadata["codegen_units"]),
            ]:
                env.pop(key, None)
                if value and value != "Cargo default":
                    env[key] = value
            execute(["cargo", "build", "--release", "--jobs", "2", "-vv",
                     "--manifest-path", consumer / "Cargo.toml"], output / config / "build", env)
            binaries = {
                "baseline": baseline / config / "cargo/release/bench-vs-openjpeg",
                "candidate": output / config / "cargo/release/bench-vs-openjpeg",
            }
            write_json(output / config / "binaries.json",
                       {key: sha(path.read_bytes()) for key, path in binaries.items()})
            for case in cases:
                work = output / config / case["id"]
                dump = execute(["taskset", "-c", options.cpu, binaries["candidate"], case["path"],
                                "dump", "0", "-", "1", "0", "0"], work / "candidate-dump", env)
                control_dump = (baseline / config / case["id"] / "rust-dump.stdout").read_bytes()
                if dump != control_dump:
                    raise ValueError(f"prototype changed output: {config}/{case['id']}")
                before, after = [], []
                for round_index in range(2):
                    order = ["baseline", "candidate"] if round_index == 0 else ["candidate", "baseline"]
                    for backend in order:
                        raw = execute(["taskset", "-c", options.cpu, binaries[backend], case["path"],
                                       "typed", "0", "-", "15", "2000", "3"],
                                      work / f"{backend}-r{round_index}", env)
                        values = []
                        for line in raw.decode("ascii").splitlines():
                            tag, value = line.split("\t")
                            if tag != "SAMPLE" or int(value) <= 0:
                                raise ValueError("invalid timing record")
                            values.append(int(value))
                        if len(values) < 15 or sum(values) < 2_000_000_000:
                            raise ValueError("incomplete timing process")
                        (before if backend == "baseline" else after).extend(values)
                        for index, value in enumerate(values):
                            row = dict(config=config, case=case["id"], **{"class": case["corpus_class"]},
                                       backend=backend, round=round_index, sample=index, ns=value)
                            writer.writerow(row)
                            raw_rows.append(row)
                        stream.flush()
                a, b = statistics.median(before) / 1e6, statistics.median(after) / 1e6
                aq = statistics.quantiles(before, n=4, method="inclusive")
                bq = statistics.quantiles(after, n=4, method="inclusive")
                aiqr, biqr = (aq[2] - aq[0]) / 1e6, (bq[2] - bq[0]) / 1e6
                summaries.append(dict(config=config, case=case["id"], **{"class": case["corpus_class"]},
                                      before_ms=a, after_ms=b, change_percent=100 * (b / a - 1),
                                      before_iqr_ms=aiqr, after_iqr_ms=biqr,
                                      inside_combined_iqr=abs(a - b) <= aiqr + biqr,
                                      exact_output=True))
            if options.numerical_299:
                numerical = []
                for path in sorted(options.numerical_299.glob("*.j2k")):
                    dumps = {}
                    for backend, binary in dict(binaries, openjpeg=baseline / config / "bench-openjpeg").items():
                        dumps[backend] = execute(
                            ["taskset", "-c", options.cpu, binary, path, "dump", "0", "-", "1", "0", "0"],
                            output / config / "299" / f"{path.stem}-{backend}", env)
                    if dumps["baseline"] != dumps["candidate"]:
                        raise ValueError(f"prototype changed #299 samples: {path.name}")
                    numerical.append(dict(case=path.name, input_sha256=sha(path.read_bytes()),
                                          before=compare_dumps(dumps["baseline"], dumps["openjpeg"]),
                                          after=compare_dumps(dumps["candidate"], dumps["openjpeg"])))
                if len(numerical) != 6:
                    raise ValueError("expected the six supplied #299 controls")
                write_json(output / config / "299.json", numerical)
    with (output / "summary.csv").open("w") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(summaries[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(summaries)
    write_json(output / "COMPLETE.json", {"observations": len(raw_rows), "summaries": summaries})


if __name__ == "__main__":
    main()
