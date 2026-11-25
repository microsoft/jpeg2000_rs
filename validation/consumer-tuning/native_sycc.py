#!/usr/bin/env python3
"""Opt-in native Rust #480 requested-sYCC comparison against the frozen oracle."""

import argparse
import json
import math
import os
from pathlib import Path
import platform
import random
import statistics
import subprocess
import sys

import native_comparison as native
from run import append, capture
from summarize import geometric, interval

HERE = native.HERE
COHORT = HERE / "native-sycc-cohort.json"
PROBE = HERE / "native-sycc-probe.rs"
COHORT_SHA = "b2aa62d8a4459f49ee47e43266047d3d242dea50af8863fc0f37599b2348662b"
BASELINE = "9279e2bad720511c2187a3602eda361ebf037287"
CANDIDATE = "d6e5f458ca6a840a94d59464d3bce400225589ac"
REVISION_PAIRS = {
    (BASELINE, CANDIDATE),
    ("f4b2b7b29d38fa31bd74263913462bb67d6e5e4e",
     "590ca79a111f701308665038a83915434d551e80"),
}
MODES = {"requested-sycc": "color", "native-off": "native"}
SCOPE = "requested-sycc-480"
ITERATIONS = 32
TIMEOUT = 120


def validate_options(options):
    native.validate_options(options.baseline, options.candidate, options.pairs, options.arch)
    if (options.baseline, options.candidate) not in REVISION_PAIRS:
        raise ValueError("requested-sYCC requires a frozen #480 baseline and candidate pair")
    if options.pairs not in (8, 24):
        raise ValueError("requested-sYCC requires 8 or 24 pairs")


def fixtures(evidence):
    raw = COHORT.read_bytes()
    if native.sha(raw) != COHORT_SHA:
        raise ValueError("requested-sYCC cohort/oracle manifest changed")
    manifest = json.loads(raw)
    if native.file_sha(PROBE) != manifest["provenance"]["probe_sha256"]:
        raise ValueError("requested-sYCC probe changed")
    (evidence / COHORT.name).write_bytes(raw)
    dst = evidence / "fixtures"
    dst.mkdir()
    for fixture, digest in manifest["fixtures"].items():
        name = f"{fixture}.jp2"
        data = (HERE / "native-sycc" / name).read_bytes()
        if native.sha(data) != digest:
            raise ValueError(f"input hash mismatch: {name}")
        (dst / name).write_bytes(data)
    return [
        {"id": f'{case["id"]}:{mode}', "name": case["id"], "mode": mode,
         "fixture": f'fixtures/{case["fixture"]}.jp2',
         "input_sha256": manifest["fixtures"][case["fixture"]],
         "discard": case["discard"], "roi": case["roi"],
         "expected_route": case["expected_route"] if mode == "requested-sycc" else "native-off",
         "expected": case["outputs"][mode]}
        for case in manifest["cases"] for mode in MODES
    ]


def command(pinned, binary, case, evidence, *, dump):
    iterations = 1 if dump else ITERATIONS
    operation = f'{MODES[case["mode"]]}-{"dump" if dump else "run"}'
    path = evidence / case["fixture"]
    if native.file_sha(path) != case["input_sha256"]:
        raise ValueError(f"input hash mismatch: {path}")
    return [*pinned, str(binary), operation, str(path), str(iterations), str(case["discard"]),
            *map(str, case["roi"] or [])]


def artifact_prefix(directory, case, label):
    # Keep the colon-delimited ID in JSON only; artifact uploads reject it in paths.
    return directory / case["name"] / case["mode"] / label


def qualify(binaries, cohort, evidence, pinned, env):
    qualified = []
    for case in cohort:
        name = case["id"]
        dumps = {}
        for label in native.BACKENDS:
            prefix = artifact_prefix(evidence / "qualification", case, label)
            prefix.parent.mkdir(parents=True, exist_ok=True)
            argv = command(pinned, binaries[label], case, evidence, dump=True)
            with prefix.with_suffix(".stdout").open("xb") as stdout, \
                    prefix.with_suffix(".stderr").open("xb") as stderr:
                result = subprocess.run(argv, env=env, stdout=stdout, stderr=stderr, timeout=TIMEOUT)
            native.write_json(prefix.with_suffix(".json"), {"argv": argv, "returncode": result.returncode})
            if result.returncode or prefix.with_suffix(".stderr").stat().st_size:
                raise ValueError(f"decoder refused or emitted diagnostics: {name}/{label}")
            dumps[label] = prefix.with_suffix(".stdout").read_bytes()
        data = dumps["baseline"]
        signature = {"sha256": native.sha(data), "bytes": len(data)}
        if data != dumps["candidate"] or signature != case["expected"]:
            raise ValueError(f"literal sample/metadata or frozen oracle mismatch: {name}")
        row = {"case": name, "mode": case["mode"], "expected_route": case["expected_route"],
               "input_sha256": case["input_sha256"], **signature}
        append(evidence / "qualification.jsonl", row)
        qualified.append(row)
    return qualified


def pair(binaries, cohort, qualified, evidence, pinned, env, pairs):
    if [row["case"] for row in qualified] != [case["id"] for case in cohort]:
        raise ValueError("all output/metadata preflights must pass before measurement")
    rows = []
    for round_index in range(pairs):
        order = list(cohort)
        random.Random(480 + round_index).shuffle(order)
        labels = native.BACKENDS if round_index % 2 == 0 else native.BACKENDS[::-1]
        for case in order:
            name = case["id"]
            for position, label in enumerate(labels):
                prefix = artifact_prefix(evidence / "processes" / f"pair-{round_index:02d}", case, label)
                argv = command(pinned, binaries[label], case, evidence, dump=False)
                metrics = native.checked(argv, prefix, env=env, seconds=TIMEOUT)
                if (metrics["wall_ns"] <= 0 or prefix.with_suffix(".stdout").stat().st_size
                        or prefix.with_suffix(".stderr").stat().st_size):
                    raise ValueError(f"invalid timing child: {name}/{label}, see {prefix}.*")
                row = {"case": name, "mode": case["mode"], "input_sha256": case["input_sha256"],
                       "backend": label, "pair": round_index, "position": position, "iterations": ITERATIONS,
                       "process_mean_ns": metrics["wall_ns"] / ITERATIONS, "metrics": metrics}
                append(evidence / "samples.jsonl", row)
                rows.append(row)
    return rows


def summaries(rows, cohort, pairs):
    results = []
    for case in cohort:
        name = case["id"]
        by_pair = {(row["pair"], row["backend"]): row for row in rows if row["case"] == name}
        times = {label: [by_pair[i, label]["process_mean_ns"] for i in range(pairs)]
                 for label in native.BACKENDS}
        ratios = [old / new for old, new in zip(times["baseline"], times["candidate"], strict=True)]
        process = {
            label: {
                "median_process_mean_ns": statistics.median(values),
                "p95_process_mean_ns": sorted(values)[math.ceil(.95 * pairs) - 1],
                "p99_process_mean_ns": sorted(values)[math.ceil(.99 * pairs) - 1],
                **{f"median_{key}": statistics.median(by_pair[i, label]["metrics"][key] for i in range(pairs))
                   for key in ("user_s", "system_s", "max_process_rss_kib",
                               "voluntary_context_switches", "involuntary_context_switches")},
            } for label, values in times.items()
        }
        results.append({"case": name, "mode": case["mode"], "expected_route": case["expected_route"],
                        "per_backend": process, "baseline_over_candidate": geometric(ratios),
                        "bootstrap95": interval(ratios), "pair_ratios": ratios})
    return results


def run(options):
    validate_options(options)
    work = options.output.resolve()
    if not work.is_relative_to(native.ROOT / "target"):
        raise ValueError("use a fresh directory within this checkout's ignored target/")
    evidence = work / "evidence"
    evidence.mkdir(parents=True, exist_ok=False)
    (work / "tmp").mkdir()
    native.reject_cargo_configs(work)
    native.clean_source(native.ROOT, evidence / "driver-status")
    native.checked(["git", "-C", str(native.ROOT), "remote", "get-url", "origin"], evidence / "driver-origin")
    if native.text(evidence / "driver-origin") not in {native.UPSTREAM, native.UPSTREAM + ".git"}:
        raise ValueError("driver checkout must come from the upstream repository")
    rust = native.pinned_tool("rustc", options.arch)
    cargo = native.pinned_tool("cargo", options.arch)
    cpus, pinned = native.native_affinity()
    revisions = dict(zip(native.BACKENDS, (options.baseline, options.candidate), strict=True))
    env = {key: os.environ[key] for key in ("PATH", "HOME") if key in os.environ}
    env["LC_ALL"] = "C"
    note = {
        "scope": SCOPE, "mode": "qualification-only" if options.qualify_only else "paired",
        "cohort_sha256": COHORT_SHA, "revisions": revisions, "pairs": options.pairs,
        "iterations": ITERATIONS, "warmups": 0, "available_cpus": cpus, "binding": pinned,
        "protocol": "fresh process; wall_ns/32 includes amortized startup and input read",
        "tails": "percentiles across process means, not per-decode latency",
        "arch": options.arch, "platform": platform.platform(), "rustc": rust, "cargo": cargo,
        "driver": capture(["git", "-C", str(native.ROOT), "rev-parse", "HEAD", "HEAD^{tree}"]),
        "lscpu": capture(["lscpu", "--json"]),
        "rustc_native_cfg": capture([rust["command"][0], "-Ctarget-cpu=native", "--print", "cfg"]),
        "run": {key: os.environ[key] for key in ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT",
                                                 "GITHUB_SHA", "ImageVersion") if key in os.environ},
    }
    native.write_json(evidence / "metadata.json", note)
    cohort = fixtures(evidence)
    native.sources(revisions, work, evidence)
    manifest = native.MANIFEST.replace("\ncodec = ", "\njpeg2000_decoder = ")
    binaries = {label: native.build(label, work, evidence, options.arch, rust, cargo,
                                    probe_source=PROBE, manifest=manifest) for label in native.BACKENDS}
    qualified = qualify(binaries, cohort, evidence, pinned, env)
    if not options.qualify_only:
        loadavg_start = os.getloadavg()
        rows = pair(binaries, cohort, qualified, evidence, pinned, env, options.pairs)
        native.write_json(evidence / "summary.json", {
            **note, "ratio": "baseline / candidate; bootstrap over matched process pairs",
            "qualified_cases": len(qualified), "loadavg_start": loadavg_start, "loadavg_end": os.getloadavg(),
            "results": summaries(rows, cohort, options.pairs),
        })


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", default=BASELINE)
    parser.add_argument("--candidate", default=CANDIDATE)
    parser.add_argument("--pairs", type=int, default=8)
    parser.add_argument("--arch", choices=native.ARCH, default=platform.machine())
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--validate-inputs", action="store_true")
    parser.add_argument("--qualify-only", action="store_true")
    options = parser.parse_args()
    try:
        validate_options(options) if options.validate_inputs else run(options)
    except (ValueError, OSError, RuntimeError, subprocess.SubprocessError) as error:
        sys.exit(f"requested-SYCC qualification: {error}")
