#!/usr/bin/env python3
"""Compare a variant with recorded full/selected/conformance outcomes, including refusals."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

from run import capture, execute, make_consumer, sha, write_json


def outcome(expected_code, expected_hash, expected_error, code, digest, error):
    if code != expected_code:
        return "changed-process-outcome"
    if code == 0:
        return "matched" if digest == expected_hash else "changed-output"
    return "matched-baseline-refusal" if error == expected_error else "changed-error"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate-source", type=Path, required=True)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--partial", type=Path, required=True)
    parser.add_argument("--conformance", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    options = parser.parse_args()
    if options.cpu not in os.sched_getaffinity(0):
        parser.error("CPU is outside allowed affinity")
    source, output = options.candidate_source.resolve(), options.output.resolve()
    if subprocess.check_output(["git", "-C", source, "status", "--porcelain"], text=True).strip():
        parser.error("commit the prototype before qualification")
    output.mkdir(parents=True, exist_ok=False)
    baseline = options.baseline.resolve()
    metadata = json.loads((baseline / "generic/build.json").read_text())
    requests = []
    for label, root in [("full", baseline)] + [
        (name, options.partial.resolve() / name) for name in ["reduce-1", "reduce-2", "reduce-3", "window"]
    ]:
        if not (root / "COMPLETE.json").is_file():
            raise ValueError(f"incomplete recorded reference: {root}")
        corpus = json.loads((root / "corpus.json").read_text())
        for case in corpus["cases"]:
            comparison = json.loads((root / "generic" / case["id"] / "correctness.json").read_text())
            requests.append(dict(id=label + "/" + case["id"], path=case["path"],
                                 input_sha256=case["sha256"], request=corpus["request"],
                                 expected_code=0, expected_hash=comparison["rust_sha256"],
                                 expected_error=""))
    external = options.conformance.resolve()
    for row in json.loads((external / "inventory.json").read_text())["records"]:
        case = row["input"]
        code = row["processes"]["rust"]["returncode"]
        expected_error = (
            (external / "observations" / Path(case["path"]).stem / "rust-dump.stderr").read_text()
            if code else ""
        )
        requests.append(dict(id="conformance/" + Path(case["path"]).stem,
                             path=str(external / case["path"]), input_sha256=case["sha256"],
                             request=dict(reduce=0, window="-"), expected_code=code,
                             expected_hash=row["comparison"]["rust_sha256"] if not code else None,
                             expected_error=expected_error))
    env = dict(os.environ, OPJ_NUM_THREADS="0", BENCH_OPENJPEG_THREADS="1",
               CARGO_TARGET_DIR=str(output / "cargo"), CARGO_PROFILE_RELEASE_DEBUG="1")
    for variable in ["RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_PROFILE_RELEASE_LTO",
                     "CARGO_PROFILE_RELEASE_CODEGEN_UNITS"]:
        env.pop(variable, None)
    manifest = make_consumer(output / "consumer", source)
    execute(["cargo", "build", "--release", "--jobs", "2", "--manifest-path", manifest],
            output / "build", env)
    binary = output / "cargo/release/bench-vs-openjpeg"
    write_json(output / "provenance.json", dict(
        scope="Exact output/error regression against recorded f4 controls; not normative conformance",
        candidate_commit=subprocess.check_output(["git", "-C", source, "rev-parse", "HEAD"], text=True).strip(),
        reference_decoder_commit=metadata["decoder_commit"], binary_sha256=sha(binary.read_bytes()),
        qualifier_sha256=sha(Path(__file__).read_bytes()), cpu=options.cpu,
        maximum_address_space=8 * 1024**3,
        driver_scope="New container-aware driver, separately built; original timing binaries not relabeled"))
    records = []
    for case in requests:
        path = Path(case["path"])
        if sha(path.read_bytes()) != case["input_sha256"]:
            raise ValueError(f"input hash changed: {case['id']}")
        prefix = output / "observations" / case["id"] / "candidate-dump"
        data, metrics = capture(
            ["taskset", "-c", options.cpu, binary, path, "dump", case["request"]["reduce"],
             case["request"]["window"], "1", "0", "0"], prefix, env,
            maximum_address_space=8 * 1024**3)
        stdout_hash = sha(data)
        digest = stdout_hash if metrics["returncode"] == 0 else None
        error = prefix.with_suffix(".stderr").read_text()
        status = outcome(case["expected_code"], case["expected_hash"], case["expected_error"],
                         metrics["returncode"], digest, error)
        record = dict(case=case["id"], input_sha256=case["input_sha256"], request=case["request"],
                      expected_code=case["expected_code"], returncode=metrics["returncode"],
                      expected_hash=case["expected_hash"], output_sha256=digest,
                      stdout_sha256=stdout_hash, status=status,
                      expected_error=case["expected_error"], error=error)
        if status in {"matched", "matched-baseline-refusal"}:
            prefix.with_suffix(".stdout").unlink()
            record["matched_stdout_omitted_after_comparison"] = True
        del data
        print(case["id"], status, flush=True)
        records.append(record)
        write_json(output / "inventory.json", records)
    all_matched = all(row["status"] in {"matched", "matched-baseline-refusal"} for row in records)
    write_json(output / "COMPLETE.json", dict(
        all_matched=all_matched, requests=len(records),
        matched_outputs=sum(row["status"] == "matched" for row in records),
        unchanged_refusals=sum(row["status"] == "matched-baseline-refusal" for row in records)))
    return 0 if all_matched else 1


if __name__ == "__main__":
    sys.exit(main())
