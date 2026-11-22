#!/usr/bin/env python3
"""Qualify the actual pinned zune JPEG 2000 consumer, not a standalone substitute."""

import argparse
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import random
import re
import shutil
import statistics
import subprocess

from measure import measure
from run import ARCHIVE_SHA256, CONFIGS, append, capture, configuration_environment, sha

HERE = Path(__file__).resolve().parent
HANDOFF = HERE / "zune-handoff"
ZUNE_PIN = "fa80e24b17ff388ac850d6042bdca391f9913c4e"
SOURCE_COMMENT = "https://github.com/microsoft/jpeg2000_rs/issues/449#issuecomment-7071726628"
BACKENDS = ("hayro", "rust")


def checked(command, **kwargs):
    subprocess.run(command, check=True, **kwargs)


def prepare(root):
    root.mkdir(parents=True, exist_ok=False)
    zune = root / "zune-image"
    checked(["git", "init", str(zune)])
    checked(["git", "-C", str(zune), "remote", "add", "origin",
             "https://github.com/etemesi254/zune-image.git"])
    checked(["git", "-C", str(zune), "fetch", "--depth", "1", "origin", ZUNE_PIN])
    checked(["git", "-C", str(zune), "switch", "--detach", "FETCH_HEAD"])
    patch = HANDOFF / "zune-jpeg2000.patch"
    checked(["git", "-C", str(zune), "apply", "--check", str(patch)])
    checked(["git", "-C", str(zune), "apply", str(patch)])
    checked(["git", "-C", str(zune), "apply", "--reverse", "--check", str(patch)])
    shutil.copytree(HANDOFF / "harness", root / "harness")
    checked(["cargo", "+1.93.1", "fetch", "--locked", "--manifest-path",
             str(root / "harness/Cargo.toml")])
    # The supplied workspace lock is 0.2.1; the independent harness already pins 0.2.2.
    checked(["cargo", "+1.93.1", "update", "--manifest-path", str(zune / "Cargo.toml"),
             "-p", "jpeg2000-decoder", "--precise", "0.2.2"])
    checked(["cargo", "+1.93.1", "test", "--locked", "--manifest-path",
             str(zune / "Cargo.toml"), "-p", "zune-image", "--no-default-features",
             "--features", "jpeg_2000_rust,jpeg", "jpeg_2000::tests"])


def fixture_names(fixtures):
    hashes = {}
    for line in (HANDOFF / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split()
        if not re.fullmatch(r"1024-(L|RGB)-(noise|smooth)-(lossless|lossy)\.(jp2|ref)", name):
            raise ValueError(f"invalid supplied fixture path: {name}")
        if sha(fixtures / name) != digest:
            raise ValueError(f"historical fixture hash mismatch: {name}")
        hashes[name] = digest
    names = sorted(name for name in hashes if name.endswith(".jp2"))
    if len(names) != 8 or len(hashes) != 16:
        raise ValueError("expected precisely eight historical inputs and references")
    if sorted(p.name for p in fixtures.glob("*.jp2")) != names:
        raise ValueError("timing directory contains a different input cohort")
    return names, hashes


def read_outcomes(tsv, pixels, fixtures, names, timed=False):
    with Path(tsv).open(newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    if [row["file"] for row in rows] != names:
        raise ValueError("harness did not report every fixture in sorted order")
    outcomes = {}
    for row in rows:
        name = row["file"]
        if row["status"] != "ok":
            raise ValueError(f"generated fixture failed: {name}: {row['status']}")
        width, height = int(row["width"]), int(row["height"])
        expected_color = "RGB" if "-RGB-" in name else "Luma"
        if (width, height, row["color"]) != (1024, 1024, expected_color):
            raise ValueError(f"invalid generated output shape: {row}")
        output = (pixels / f"{name}.bin").read_bytes()
        reference = (fixtures / name).with_suffix(".ref").read_bytes()
        if len(output) != len(reference) or len(output) != 1024 * 1024 * (3 if "-RGB-" in name else 1):
            raise ValueError(f"output byte count changed: {name}")
        if "lossless" in name and output != reference:
            raise ValueError(f"lossless source recovery failed: {name}")
        if timed and (int(row["runs"]) != 15 or float(row["p50_us"]) <= 0
                      or float(row["p90_us"]) < float(row["p50_us"])):
            raise ValueError(f"invalid measured timing row: {row}")
        outcomes[name] = {
            "width": width, "height": height, "color": row["color"], "bytes": len(output),
            "sha256": hashlib.sha256(output).hexdigest(),
            "reference_sha256": hashlib.sha256(reference).hexdigest(),
            "reference_bytes_changed": sum(a != b for a, b in zip(output, reference)),
            "reference_max_abs_error": max(abs(a - b) for a, b in zip(output, reference)),
        }
    return rows, outcomes


def native_cpu():
    observed = capture(["rustc", "+1.93.1", "--print", "target-cpus"])
    if observed["returncode"]:
        raise ValueError("cannot inspect native CPU target")
    match = re.search(r"\bnative\s+-[^\n]*\(currently ([^)]+)\)", observed["stdout"])
    if match is None or not re.fullmatch(r"[a-zA-Z0-9_-]+", match[1]) or match[1] == "generic":
        raise ValueError("compiler did not identify an explicit native CPU target")
    return match[1], observed


def compiler_records(invocations, config, cpu):
    records = {}
    for path in invocations.glob("rustc-*.metrics.json"):
        record = json.loads(path.read_text())
        args = record["command"]
        if "--crate-name" in args:
            name = args[args.index("--crate-name") + 1]
            if name in {"zune_jp2_compare", "zune_image", "jpeg2000_decoder", "hayro_jpeg2000"}:
                records.setdefault(name, []).append(record)
    if set(records) != {"zune_jp2_compare", "zune_image", "jpeg2000_decoder", "hayro_jpeg2000"}:
        raise ValueError(f"missing actual consumer/decoder compiler invocations: {records.keys()}")
    for name, rows in records.items():
        if len(rows) != 1:
            raise ValueError(f"expected one cold compilation of {name}, got {len(rows)}")
        flags = " ".join(rows[0]["command"])
        required = ["opt-level=3", f"codegen-units={CONFIGS[config][2]}"]
        if config in {"cpu", "combined"}:
            required.append(f"target-cpu={cpu}")
        elif "target-cpu=" in flags:
            raise ValueError("generic cell unexpectedly contains CPU tuning")
        if not all(flag in flags for flag in required):
            raise ValueError(f"actual {name} flags differ from {config}: {flags}")
    final = " ".join(records["zune_jp2_compare"][0]["command"])
    if ("lto=thin" in final) != (config in {"thinlto", "combined"}):
        raise ValueError(f"actual final-link LTO differs from {config}")
    return records


def reductions(samples, backend, config, names, pairs):
    logs = []
    per_fixture = {}
    for name in names:
        matched = []
        for pair in range(pairs):
            values = {
                row["config"]: float(next(r for r in row["rows"] if r["file"] == name)["p50_us"])
                for row in samples if row["backend"] == backend and row["tuned"] == config
                and row["pair"] == pair
            }
            matched.append(math.log(values[config] / values["generic"]))
        per_fixture[name] = 100 * (1 - math.exp(statistics.mean(matched)))
    for pair in range(pairs):
        matched = []
        for name in names:
            values = {
                row["config"]: float(next(r for r in row["rows"] if r["file"] == name)["p50_us"])
                for row in samples if row["backend"] == backend and row["tuned"] == config
                and row["pair"] == pair
            }
            matched.append(math.log(values[config] / values["generic"]))
        logs.append(statistics.mean(matched))
    rng = random.Random(449)
    draws = sorted(100 * (1 - math.exp(statistics.mean(rng.choices(logs, k=pairs))))
                   for _ in range(5000))
    return {"decode_time_reduction_percent": 100 * (1 - math.exp(statistics.mean(logs))),
            "paired_bootstrap95_percent": [draws[125], draws[4874]],
            "per_fixture_reduction_percent": per_fixture,
            "resampling_unit": "matched process-pair block; eight correlated inputs not independent"}


def run(options):
    if platform.system() != "Linux" or platform.machine() not in {"x86_64", "aarch64"}:
        raise ValueError("use a native x86_64/aarch64 Linux host")
    if options.pairs < 2 or options.pairs % 2:
        raise ValueError("--pairs must be even and at least two")
    output = options.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    root, fixtures = options.work_root.resolve(), options.fixtures.resolve()
    names, hashes = fixture_names(fixtures)
    if capture(["git", "-C", str(root / "zune-image"), "rev-parse", "HEAD"])["stdout"].strip() != ZUNE_PIN:
        raise ValueError("consumer checkout differs from the handoff pin")
    if sha(root / "harness/Cargo.lock") != sha(HANDOFF / "harness/Cargo.lock"):
        raise ValueError("supplied harness lock changed")
    cpu, cpu_info = native_cpu()
    allowed = os.sched_getaffinity(0)
    affinity = str(min(allowed))
    version = capture(["rustc", "+1.93.1", "-vV"])
    if version["returncode"] or "release: 1.93.1\n" not in version["stdout"]:
        raise ValueError("required native compiler pin unavailable")
    metadata = {
        "source_comment": SOURCE_COMMENT, "zune_pin": ZUNE_PIN,
        "patch_sha256": sha(HANDOFF / "zune-jpeg2000.patch"), "fixture_hashes": hashes,
        "harness_lock_sha256": sha(root / "harness/Cargo.lock"),
        "root_workspace_lock_sha256": sha(root / "zune-image/Cargo.lock"),
        "patch_status": capture(["git", "-C", str(root / "zune-image"), "status", "--short"]),
        "source_diff": capture(["git", "-C", str(root / "zune-image"), "diff", "--binary"]),
        "platform": platform.platform(), "machine": platform.machine(), "lscpu": capture(["lscpu", "--json"]),
        "rustc": version, "native_cpu": cpu, "target_cpus": cpu_info,
        "generic_cfg": capture(["rustc", "+1.93.1", "--print", "cfg"]),
        "tuned_cfg": capture(["rustc", "+1.93.1", "-Ctarget-cpu=" + cpu, "--print", "cfg"]),
        "affinity": affinity, "pairs": options.pairs, "build_rounds": 2,
        "coverage": {"actual_patched_zune_consumer": True, "standalone_substitute": False,
                     "pdfium": False, "native_not_emulated": True},
    }
    (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    cargo_home = Path(os.environ.get("CARGO_HOME", str(Path.home() / ".cargo")))
    archives = list((cargo_home / "registry/cache").glob("*/jpeg2000-decoder-0.2.2.crate"))
    if len(archives) != 1 or sha(archives[0]) != ARCHIVE_SHA256:
        raise ValueError("actual published 0.2.2 archive changed")
    for backend in BACKENDS:
        command = ["cargo", "+1.93.1", "tree", "--locked", "--manifest-path",
                   str(root / "harness/Cargo.toml"), "-e", "features"]
        if backend == "rust":
            command += ["--features", "candidate"]
        graph = capture(command)
        (output / f"features-{backend}.json").write_text(json.dumps(graph, indent=2) + "\n")
        if graph["returncode"]:
            raise ValueError("actual feature graph unavailable")
    binaries, references, samples, builds, build_qualification = {}, {}, [], [], {}
    combinations = [(config, backend) for config in CONFIGS for backend in BACKENDS]
    for round_index in range(2):
        for config, backend in combinations if round_index == 0 else reversed(combinations):
            label = f"build-{round_index}-{config}-{backend}"
            directory = output / label
            invocations = directory / "invocations"
            invocations.mkdir(parents=True)
            target = directory / "target"
            env = configuration_environment(config, target, invocations)
            env["RUSTFLAGS"] = env["RUSTFLAGS"].replace("-Ctarget-cpu=native", "-Ctarget-cpu=" + cpu)
            command = ["cargo", "+1.93.1", "build", "--locked", "--offline", "--release",
                       "--manifest-path", str(root / "harness/Cargo.toml"), "-vv", "--timings"]
            if backend == "rust":
                command += ["--features", "candidate"]
            metrics = measure(command, directory / "cargo", env=env, sample_tree=True)
            if metrics["returncode"]:
                raise ValueError(f"actual consumer build failed: {label}")
            records = compiler_records(invocations, config, cpu)
            binary = output / "binaries" / label
            binary.parent.mkdir(exist_ok=True)
            shutil.copyfile(target / "release/zune-jp2-compare", binary)
            binary.chmod(0o755)
            binaries[config, backend] = binary
            info = {"round": round_index, "config": config, "backend": backend, "metrics": metrics,
                    "binary_sha256": sha(binary), "binary_bytes": binary.stat().st_size,
                    "sections": capture(["size", "-A", str(binary)]), "compiler_records": records}
            builds.append(info)
            append(output / "builds.jsonl", info)
            prefix = output / "acceptance" / label
            pixels = prefix.parent / (label + "-pixels")
            check = measure([binary, "strict", fixtures, pixels], prefix)
            if check["returncode"]:
                raise ValueError(f"consumer acceptance process failed: {label}")
            _, outcomes = read_outcomes(Path(str(prefix) + ".stdout"), pixels, fixtures, names)
            references.setdefault(backend, outcomes)
            key = (backend, config)
            build_qualification[key] = build_qualification.get(key, True) and outcomes == references[backend]
            append(output / "acceptance.jsonl", {"round": round_index, "config": config,
                                               "backend": backend, "outcomes": outcomes,
                                               "matches_backend_generic": outcomes == references[backend]})
            if not target.resolve().is_relative_to(output) or target.name != "target":
                raise ValueError("unexpected compiler-cache cleanup path")
            shutil.rmtree(target)
            print(f"built and checked {label}", flush=True)
    for pair in range(options.pairs):
        tuned = list(CONFIGS)[1:]
        if pair % 2:
            tuned.reverse()
        for config in tuned:
            for backend in BACKENDS if pair % 2 == 0 else reversed(BACKENDS):
                for position, selected in enumerate(("generic", config) if pair % 2 == 0 else (config, "generic")):
                    label = f"p{pair}-{config}-{backend}-{position}"
                    prefix = output / "samples" / label
                    pixels = prefix.parent / (label + "-pixels")
                    metrics = measure(["taskset", "-c", affinity, binaries[selected, backend],
                                       "bench", fixtures, pixels], prefix)
                    if metrics["returncode"]:
                        raise ValueError(f"consumer timing process failed: {label}")
                    rows, outcomes = read_outcomes(Path(str(prefix) + ".stdout"), pixels, fixtures, names, timed=True)
                    record = {"pair": pair, "tuned": config, "position": position, "config": selected,
                              "backend": backend, "metrics": metrics, "rows": rows, "outcomes": outcomes,
                              "matches_backend_generic": outcomes == references[backend]}
                    samples.append(record)
                    append(output / "samples.jsonl", record)
            print(f"completed paired block {pair} {config}", flush=True)
    results = {}
    for backend in BACKENDS:
        results[backend] = {}
        for config in list(CONFIGS)[1:]:
            matching = [r for r in samples if r["backend"] == backend and r["tuned"] == config]
            qualified = (build_qualification[backend, config]
                         and build_qualification[backend, "generic"]
                         and all(r["matches_backend_generic"] for r in matching))
            results[backend][config] = {"qualified": qualified,
                "timing": reductions(samples, backend, config, names, options.pairs) if qualified else None,
                "reason": None if qualified else "backend output differs from its own generic baseline"}
    (output / "summary.json").write_text(json.dumps({
        "results": results, "builds": len(builds), "processes": len(samples),
        "coverage": metadata["coverage"], "lossy_oracle_differences": references,
        "note": "Matched native zune decoder+Image creation/drop; flattening/I/O/reference checks excluded from timing. "
                "Process RSS includes harness/input/output work; tree RSS is sampled and may double-count shared pages.",
    }, indent=2) + "\n")
    (output / "COMPLETE").write_text("actual consumer builds, hashes, outcomes and paired timings recorded\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    setup = commands.add_parser("prepare")
    setup.add_argument("--work-root", type=Path, required=True)
    bench = commands.add_parser("run")
    bench.add_argument("--work-root", type=Path, required=True)
    bench.add_argument("--fixtures", type=Path, required=True)
    bench.add_argument("--output", type=Path, required=True)
    bench.add_argument("--pairs", type=int, default=4)
    options = parser.parse_args()
    if options.command == "prepare":
        prepare(options.work_root.resolve())
    else:
        run(options)
