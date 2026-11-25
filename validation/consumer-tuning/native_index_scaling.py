#!/usr/bin/env python3
"""Opt-in native #481 seeded32 fixed-pixel scaling qualification."""

import argparse
import json
import os
from pathlib import Path
import platform
import random
import re
import shutil
import struct
import subprocess
import sys

import native_comparison as native
from run import append, capture

BASELINE = "f4b2b7b29d38fa31bd74263913462bb67d6e5e4e"
CANDIDATE = "2743436c341a679ce62162f3fc3ef72807b98dee"
SCOPE = "fixed-pixel-index-scaling-481"
PROBE = native.HERE / "native-index-scaling-probe.rs"
PROBE_SHA = "7a7fdba84ad8299a5825d46d8b054424d83cc914736893124613fcf1a31cb216"
COHORT = native.HERE / "native-index-scaling-cohort.json"
COHORT_SHA = "a39c347e707e1c68af82644b7465fe1c808129a31ab0c0216361da4715ce0297"
FIXTURES = native.HERE / "native-index-scaling"
PGM_SHA = "2d90e72ea5bacbac55fd8bdef05309f54beca92e52977939eef1d79295d58fd9"
GRID = (1, 4, 16, 64, 256, 1024)
ORDERS = ("grouped", "interleaved")
CASES = tuple(
    {"id": f"k{k:04d}-{order}", "fixture": f"k{k:04d}-{order}", "K": k,
     "order": order, "mode": "full", "group": "fixed32x32-full"}
    for k in GRID for order in ORDERS
) + ({"id": "k1024-interleaved-lastpixel-roi", "fixture": "k1024-interleaved",
      "K": 1024, "order": "interleaved", "mode": "roi", "group": "fixed32x32-roi-one"},)
TIMEOUT = 180


def validate_options(options):
    native.validate_options(options.baseline, options.candidate, options.pairs, options.arch)
    if (options.baseline, options.candidate) != (BASELINE, CANDIDATE) or options.pairs != 8:
        raise ValueError("index scaling requires the exact approved f4b/274 pair and 8 pairs")


def source_pixels():
    state = 0x48103232
    pixels = []
    for _ in range(1024):
        state = (1664525 * state + 1013904223) & 0xFFFFFFFF
        pixels.append(state >> 24)
    return pixels


def expected(mode):
    pixels = source_pixels()
    extent, origin, samples = (32, 0, pixels) if mode == "full" else (1, 31, pixels[-1:])
    if mode not in ("full", "roi"):
        raise ValueError("expected full or roi")
    return (
        f"TypedImage {{ width: {extent}, height: {extent}, x_origin: {origin}, "
        f"y_origin: {origin}, components: [TypedComponent {{ width: {extent}, height: {extent}, "
        "info: ComponentInfo { precision: 8, signed: false, x_subsampling: 1, "
        "y_subsampling: 1, x_registration: 0, y_registration: 0 }, "
        f"samples: Unsigned({samples}), channel_definitions: [] }}] }}\n"
    ).encode()


def part_groups(data, k):
    """Validate the frozen simple SOT/Psot recipe without decoding or rewriting."""
    if data[:2] != b"\xffO":
        raise ValueError("expected raw SOC")
    position = 2
    while data[position:position + 2] != b"\xff\x90":
        marker = int.from_bytes(data[position:position + 2], "big")
        if marker not in {0xFF51, 0xFF52, 0xFF5C, 0xFF64} or position + 4 > len(data):
            raise ValueError("unexpected/offset-dependent scaling header")
        length = struct.unpack_from(">H", data, position + 2)[0]
        if length < 2 or position + 2 + length > len(data):
            raise ValueError("invalid scaling header length")
        position += 2 + length
    prefix = data[:position]
    sequence, groups = [], {tile: [] for tile in range(k)}
    while data[position:position + 2] == b"\xff\x90":
        if position + 14 > len(data):
            raise ValueError("truncated SOT")
        length, tile, size, ordinal, count = struct.unpack_from(">HHIBB", data, position + 2)
        if (length != 10 or tile >= k or count != 3 or size < 14
                or position + size > len(data) or data[position + 12:position + 14] != b"\xff\x93"):
            raise ValueError("invalid actual scaling SOT/Psot")
        sequence.append((tile, ordinal))
        groups[tile].append(data[position:position + size])
        position += size
    if data[position:] != b"\xff\xd9" or len(sequence) != 3 * k:
        raise ValueError("invalid actual scaling part count/EOC")
    return prefix, sequence, groups


def stage_inputs(evidence):
    raw = COHORT.read_bytes()
    if native.sha(raw) != COHORT_SHA or native.file_sha(PROBE) != PROBE_SHA:
        raise ValueError("scaling cohort/probe hash mismatch")
    cohort = json.loads(raw)
    required = {(k, order) for k in GRID for order in ORDERS}
    if (len(cohort["fixtures"]) != 12
            or {(row["K"], row["order"]) for row in cohort["fixtures"]} != required):
        raise ValueError("changed scaling matrix")
    pgm = (FIXTURES / "seeded32.pgm").read_bytes()
    if native.sha(pgm) != PGM_SHA or pgm != b"P5\n32 32\n255\n" + bytes(source_pixels()):
        raise ValueError("scaling PGM differs from independent seeded source")
    folder = evidence / "fixtures"
    folder.mkdir()
    (folder / "seeded32.pgm").write_bytes(pgm)
    (evidence / PROBE.name).write_bytes(PROBE.read_bytes())
    (evidence / COHORT.name).write_bytes(raw)
    facts, records = {}, {}
    for row in cohort["fixtures"]:
        name = f"k{row['K']:04d}-{row['order']}"
        if row["id"] != name or row["path"] != name + ".j2k" or row["P"] != 3 * row["K"]:
            raise ValueError("changed scaling fixture identity")
        data = native.checked_bytes((FIXTURES / row["path"]).read_bytes(), row)
        prefix, sequence, groups = part_groups(data, row["K"])
        order = ([(tile, ordinal) for tile in range(row["K"]) for ordinal in range(3)]
                 if row["order"] == "grouped" else
                 [(tile, ordinal) for ordinal in range(3) for tile in range(row["K"])])
        if sequence != order:
            raise ValueError(f"changed actual physical scaling order: {name}")
        facts[row["K"], row["order"]] = (prefix, groups)
        records[name] = row
        (folder / row["path"]).write_bytes(data)
    for k in GRID:
        if facts[k, "grouped"] != facts[k, "interleaved"]:
            raise ValueError(f"per-tile bytes/header differ between physical orders: K{k}")
    native.write_json(evidence / "fixture-manifest.json", {
        "cohort_sha256": COHORT_SHA, "provenance": cohort,
        "source_pgm_sha256": PGM_SHA, "cases": CASES,
        "actual_part_counts": {name: row["P"] for name, row in records.items()},
    })
    return records


def command(pinned, binary, operation, case, evidence, fixtures):
    row = fixtures[case["fixture"]]
    path = evidence / "fixtures" / row["path"]
    pgm = evidence / "fixtures/seeded32.pgm"
    if native.file_sha(path) != row["sha256"] or native.file_sha(pgm) != PGM_SHA:
        raise ValueError("staged scaling input hash mismatch")
    return [*pinned, str(binary), operation, case["mode"], str(path), str(pgm)]


def qualify(binaries, fixtures, evidence, pinned, env):
    qualified = []
    for case in CASES:
        oracle = expected(case["mode"])
        for label in native.BACKENDS:
            prefix = evidence / "qualification" / case["id"] / label
            native.checked(command(pinned, binaries[label], "preflight", case, evidence, fixtures),
                           prefix, env=env, seconds=TIMEOUT)
            if (prefix.with_suffix(".stderr").stat().st_size
                    or prefix.with_suffix(".stdout").read_bytes() != oracle):
                raise ValueError(f"scaling full literal oracle mismatch or diagnostics: {case['id']}/{label}")
            append(evidence / "qualification.jsonl", {
                "case": case["id"], "backend": label, "literal_bytes": len(oracle),
                "literal_sha256": native.sha(oracle), "oracle": "independent-seeded-PGM-all-fields",
            })
            qualified.append((case["id"], label))
    return qualified


def timings(raw):
    lines = raw.splitlines()
    if (len(lines) != 5 or re.fullmatch(rb"CONFIG\t3\t1\t[0-9]{1,39}", lines[0]) is None
            or lines[-1] != b"LIFECYCLE\t6\t3"
            or any(re.fullmatch(rb"SAMPLE\t[1-9][0-9]{0,38}", line) is None for line in lines[1:4])):
        raise ValueError("changed scaling six-call/three-clock protocol")
    return int(lines[0].split(b"\t")[3]), [int(line.split(b"\t")[1]) for line in lines[1:4]]


def pair(binaries, fixtures, qualified, evidence, pinned, env, pairs):
    required = [(case["id"], label) for case in CASES for label in native.BACKENDS]
    if qualified != required:
        raise ValueError("all 26 scaling full literal preflights must pass before timing")
    rows = []
    for index in range(pairs):
        cases = list(CASES)
        random.Random(48132 + index).shuffle(cases)
        labels = native.BACKENDS if index % 2 == 0 else native.BACKENDS[::-1]
        for case_index, case in enumerate(cases):
            for position, label in enumerate(labels):
                prefix = evidence / "processes" / f"pair-{index:02d}" / case["id"] / label
                metrics = native.checked(
                    command(pinned, binaries[label], "bench-fixed", case, evidence, fixtures),
                    prefix, env=env, seconds=TIMEOUT)
                calibration, samples = timings(prefix.with_suffix(".stdout").read_bytes())
                if prefix.with_suffix(".stderr").stat().st_size:
                    raise ValueError(f"scaling timed diagnostics: {prefix}")
                row = {"fixture": case["id"], "K": case["K"], "mode": case["mode"],
                       "input_sha256": fixtures[case["fixture"]]["sha256"], "backend": label,
                       "pair": index, "case_index": case_index, "position": position,
                       "decode_ns": samples, "calibration_ns": calibration,
                       "complete_api_calls": 6, "timed_api_calls": 3, "metrics": metrics}
                append(evidence / "samples.jsonl", row)
                rows.append(row)
    return rows


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
    fixtures = stage_inputs(evidence)
    rust, cargo = (native.pinned_tool(tool, options.arch) for tool in ("rustc", "cargo"))
    cpus, pinned = native.native_affinity()
    revisions = dict(zip(native.BACKENDS, (options.baseline, options.candidate), strict=True))
    env = {key: os.environ[key] for key in ("PATH", "HOME") if key in os.environ}
    env["LC_ALL"] = "C"
    note = {
        "scope": SCOPE, "mode": "qualification-only" if options.qualify_only else "paired",
        "revisions": revisions, "pairs": options.pairs, "harness_sha256": PROBE_SHA,
        "cohort_sha256": COHORT_SHA, "source_pgm_sha256": PGM_SHA, "cases": CASES,
        "complete_api_calls_per_timed_child": 6, "timed_api_calls_per_child": 3,
        "protocol": "first qualified decode, one warmup, one calibration, three fixed decode-and-drop clocks; no 512 batch",
        "timed_children": 13 * 2 * options.pairs, "literal_preflights_before_timing": 26,
        "available_cpus": cpus, "binding": pinned, "arch": options.arch,
        "platform": platform.platform(), "rustc": rust, "cargo": cargo,
        "metrics": "GNU time covers whole child; API clocks cover the final three calls; no exclusions",
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
        folder = evidence / label
        receipt = json.loads((folder / "binary.json").read_text())
        if (receipt["harness_sha256"] != PROBE_SHA
                or [arg for arg in receipt["decoder_argv"] if arg.startswith("feature=")] != ['feature="default"']
                or any(arg.startswith("feature=") for arg in receipt["argv"])):
            raise ValueError(f"scaling probe source/features changed: {label}")
        recorded = folder / "recorded-native-probe"
        shutil.copyfile(binaries[label], recorded)
        if native.file_sha(recorded) != receipt["sha256"]:
            raise ValueError(f"recorded scaling ELF hash mismatch: {label}")
        native.write_json(folder / "recorded-binary.json", {
            "path": str(recorded.relative_to(evidence)), "sha256": receipt["sha256"],
            "elf_machine": receipt["elf_machine"],
        })
        native.checked(["git", "-C", str(work / label / "source"), "ls-tree", "-r", "--full-tree", "HEAD"],
                       folder / "source-tree")
    qualified = qualify(binaries, fixtures, evidence, pinned, env)
    if not options.qualify_only:
        loadavg = os.getloadavg()
        rows = pair(binaries, fixtures, qualified, evidence, pinned, env, options.pairs)
        native.write_json(evidence / "summary.json", {
            **note, "qualified_checks": len(qualified), "record_count": len(rows),
            "complete_timed_child_api_calls": 6 * len(rows),
            "ratio": "candidate / baseline; matched process pairs, no exclusions",
            "loadavg_start": loadavg, "loadavg_end": os.getloadavg(),
            "results": native.summarize(rows, list(CASES), options.pairs),
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
        sys.exit(f"native index scaling qualification: {error}")
