#!/usr/bin/env python3
"""Opt-in native comparison of the frozen #481 selected tile-part experiment."""

import argparse
import json
import math
import os
from pathlib import Path
import platform
import random
import re
import statistics
import subprocess
import sys

import native_comparison as native
from run import append, capture
from summarize import geometric, interval

BASELINE = "9279e2bad720511c2187a3602eda361ebf037287"
CANDIDATE = "e21eb47936be4c6310a38498df5ab255a2648cbf"
REVISION_PAIRS = {
    (BASELINE, CANDIDATE),
    ("f4b2b7b29d38fa31bd74263913462bb67d6e5e4e",
     "9e2881fc6e057ecaa9b1b003a7519f9e28bbee1b"),
    ("f4b2b7b29d38fa31bd74263913462bb67d6e5e4e",
     "2743436c341a679ce62162f3fc3ef72807b98dee"),
}
SCOPE = "selected-parts-481"
PROBE = native.HERE / "native-selected-parts-probe.rs"
PROBE_SHA = "d8646e85db9c851ac093f3bd097aa92a70b25606ccdc2e1b641db16d6c2002be"
FIXTURES = {
    "grouped": "5e73c697e14e9d669ef58c2438a70cd55b1cba8c888633374bb7e47b656a0eef",
    "interleaved": "eeae0a6f3927776a2446cca9293d0f58d719e4efff50c2f96ed81e6b84f8c5df",
}
PREFLIGHTS = tuple((fixture, mode) for fixture in FIXTURES for mode in ("full", "roi"))
CASES = (("grouped", "full"), ("interleaved", "full"), ("interleaved", "roi"))
ITERATIONS, WARMUPS, TIMEOUT = 512, 2, 120


def stage_inputs(evidence):
    probe = PROBE.read_bytes()
    if native.sha(probe) != PROBE_SHA:
        raise ValueError("selected probe hash mismatch")
    (evidence / PROBE.name).write_bytes(probe)
    fixtures = evidence / "fixtures"
    fixtures.mkdir()
    for fixture, digest in FIXTURES.items():
        name = f"{fixture}.j2k"
        data = (native.HERE / "native-selected-parts" / name).read_bytes()
        if len(data) != 1027 or native.sha(data) != digest:
            raise ValueError(f"selected fixture hash/length mismatch: {name}")
        (fixtures / name).write_bytes(data)


def expected(mode):
    # Empty packets in every tile/layer leave unsigned 8-bit samples at midscale.
    width, x = {"full": (32, 0), "roi": (1, 31)}[mode]
    return (
        f"TypedImage {{ width: {width}, height: 1, x_origin: {x}, y_origin: 0, "
        f"components: [TypedComponent {{ width: {width}, height: 1, info: ComponentInfo {{ "
        "precision: 8, signed: false, x_subsampling: 1, y_subsampling: 1, "
        "x_registration: 0, y_registration: 0 }, "
        f"samples: Unsigned({[128] * width}), channel_definitions: [] }}] }}\n"
    ).encode()


def command(pinned, binary, operation, case, evidence):
    if case is None:
        return [*pinned, str(binary), operation]
    fixture, mode = case
    path = evidence / "fixtures" / f"{fixture}.j2k"
    if native.file_sha(path) != FIXTURES[fixture]:
        raise ValueError(f"selected fixture hash mismatch: {path}")
    return [*pinned, str(binary), operation, mode, str(path)]


def qualify(binaries, evidence, pinned, env):
    qualified = []
    for case in (None, *PREFLIGHTS):
        name = "self-check" if case is None else "-".join(case)
        operation = "self-check" if case is None else "preflight"
        oracle = b"SELF-CHECK\tPASS\n" if case is None else expected(case[1])
        for label in native.BACKENDS:
            prefix = evidence / "qualification" / name / label
            argv = command(pinned, binaries[label], operation, case, evidence)
            native.checked(argv, prefix, env=env, seconds=TIMEOUT)
            if (prefix.with_suffix(".stderr").stat().st_size
                    or prefix.with_suffix(".stdout").read_bytes() != oracle):
                raise ValueError(f"selected literal oracle mismatch or diagnostics: {name}/{label}")
            append(evidence / "qualification.jsonl", {
                "case": name, "backend": label, "literal_bytes": len(oracle),
                "literal_sha256": native.sha(oracle),
            })
            qualified.append((name, label))
    return qualified


def pair(binaries, qualified, evidence, pinned, env, pairs):
    required = [(name, label) for name in ("self-check", *map("-".join, PREFLIGHTS))
                for label in native.BACKENDS]
    if required != qualified:
        raise ValueError("all selected literal preflights and negative self-checks must pass")
    rows = []
    for index in range(pairs):
        order = list(CASES)
        random.Random(481 + index).shuffle(order)
        labels = native.BACKENDS if index % 2 == 0 else native.BACKENDS[::-1]
        for case in order:
            name = "-".join(case)
            for position, label in enumerate(labels):
                prefix = evidence / "processes" / f"pair-{index:02d}" / name / label
                argv = command(pinned, binaries[label], "bench-fixed", case, evidence)
                metrics = native.checked(argv, prefix, env=env, seconds=TIMEOUT)
                raw = prefix.with_suffix(".stdout").read_bytes()
                match = re.fullmatch(rb"BATCH\t512\t2\t([1-9][0-9]{0,38})\n", raw)
                if match is None or prefix.with_suffix(".stderr").stat().st_size:
                    raise ValueError(f"invalid fixed batch output: see {prefix}.*")
                batch_ns = int(match[1])
                row = {"case": name, "input_sha256": FIXTURES[case[0]], "backend": label,
                       "pair": index, "position": position, "batch_ns": batch_ns,
                       "batch_mean_ns": batch_ns / ITERATIONS, "metrics": metrics}
                append(evidence / "samples.jsonl", row)
                rows.append(row)
    return rows


def summaries(rows, pairs):
    output = []
    for case in CASES:
        name = "-".join(case)
        selected = [row for row in rows if row["case"] == name]
        by_pair = {(row["pair"], row["backend"]): row for row in selected}
        if len(selected) != 2 * pairs or len(by_pair) != 2 * pairs:
            raise ValueError(f"missing or duplicate process pairs: {name}")
        times = {label: [by_pair[i, label]["batch_mean_ns"] for i in range(pairs)]
                 for label in native.BACKENDS}
        ratios = [old / new for old, new in zip(times["baseline"], times["candidate"], strict=True)]
        output.append({
            "case": name, "baseline_over_candidate": geometric(ratios),
            "bootstrap95": interval(ratios), "pair_ratios": ratios,
            "per_backend": {label: {
                "median_batch_mean_ns": statistics.median(values),
                "p95_batch_mean_ns": sorted(values)[math.ceil(.95 * pairs) - 1],
                "p99_batch_mean_ns": sorted(values)[math.ceil(.99 * pairs) - 1],
                **{f"median_{key}": statistics.median(by_pair[i, label]["metrics"][key] for i in range(pairs))
                   for key in ("user_s", "system_s", "max_process_rss_kib", "minor_faults", "major_faults",
                               "voluntary_context_switches", "involuntary_context_switches")},
            } for label, values in times.items()},
        })
    return output


def run(options):
    native.validate_options(options.baseline, options.candidate, options.pairs, options.arch)
    if (options.baseline, options.candidate) not in REVISION_PAIRS or options.pairs not in (8, 24):
        raise ValueError("selected parts requires the frozen #481 revisions and 8 or 24 pairs")
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
    stage_inputs(evidence)
    rust = native.pinned_tool("rustc", options.arch)
    cargo = native.pinned_tool("cargo", options.arch)
    cpus, pinned = native.native_affinity()
    revisions = dict(zip(native.BACKENDS, (options.baseline, options.candidate), strict=True))
    env = {key: os.environ[key] for key in ("PATH", "HOME") if key in os.environ}
    env["LC_ALL"] = "C"
    note = {
        "scope": SCOPE, "mode": "qualification-only" if options.qualify_only else "paired",
        "revisions": revisions, "pairs": options.pairs, "harness_sha256": PROBE_SHA,
        "input_sha256": FIXTURES, "timed_cases": CASES,
        "iterations": ITERATIONS, "warmups": WARMUPS, "available_cpus": cpus, "binding": pinned,
        "protocol": "one fresh child per side/case/pair; clocked batch_ns/512 excludes startup, input and warmups",
        "tails": "percentiles across process batch means, not independent per-decode latency",
        "metrics": "GNU time CPU/RSS/faults/context switches cover the entire child",
        "arch": options.arch, "platform": platform.platform(), "rustc": rust, "cargo": cargo,
        "driver": capture(["git", "-C", str(native.ROOT), "rev-parse", "HEAD", "HEAD^{tree}"]),
        "lscpu": capture(["lscpu", "--json"]),
        "rustc_native_cfg": capture([rust["command"][0], "-Ctarget-cpu=native", "--print", "cfg"]),
        "run": {key: os.environ[key] for key in ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT",
                                                 "GITHUB_SHA", "ImageVersion") if key in os.environ},
    }
    native.write_json(evidence / "metadata.json", note)
    native.sources(revisions, work, evidence)
    manifest = native.MANIFEST.replace(", default-features = false", "")
    binaries = {label: native.build(label, work, evidence, options.arch, rust, cargo,
                                    probe_source=evidence / PROBE.name, manifest=manifest)
                for label in native.BACKENDS}
    for label in native.BACKENDS:
        receipt = json.loads((evidence / label / "binary.json").read_text())
        if (receipt["harness_sha256"] != PROBE_SHA
                or [arg for arg in receipt["decoder_argv"] if arg.startswith("feature=")] != ['feature="default"']
                or any(arg.startswith("feature=") for arg in receipt["argv"])):
            raise ValueError(f"selected probe source or feature binding changed: {label}")
    qualified = qualify(binaries, evidence, pinned, env)
    if not options.qualify_only:
        loadavg = os.getloadavg()
        rows = pair(binaries, qualified, evidence, pinned, env, options.pairs)
        native.write_json(evidence / "summary.json", {
            **note, "qualified_checks": len(qualified), "loadavg_start": loadavg, "loadavg_end": os.getloadavg(),
            "ratio": "baseline / candidate; bootstrap over matched process pairs, no exclusions",
            "results": summaries(rows, options.pairs),
        })


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", default=BASELINE)
    parser.add_argument("--candidate", default=CANDIDATE)
    parser.add_argument("--pairs", type=int, default=8)
    parser.add_argument("--arch", choices=native.ARCH, default=platform.machine())
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--qualify-only", action="store_true")
    try:
        run(parser.parse_args())
    except (ValueError, OSError, RuntimeError, subprocess.SubprocessError) as error:
        sys.exit(f"selected tile-part qualification: {error}")
