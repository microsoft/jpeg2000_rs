#!/usr/bin/env python3
"""Manual, focused, paired baseline/candidate comparison of native Rust consumers."""

import argparse
import json
import math
import os
from pathlib import Path
import platform
import random
import re
import shutil
import statistics
import struct
import sys

from generate_fixtures import jp2_parts, sha
from measure import measure
from run import append, capture, configuration_environment
from summarize import geometric, interval

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
UPSTREAM = "https://github.com/microsoft/jpeg2000_rs"
RUST = "+1.93.1"
ARCH = {"x86_64": (62, "X64"), "aarch64": (183, "ARM64")}
BACKENDS = ("baseline", "candidate")
LEGACY = ("noisy-gray-lossless", "smooth-rgb-lossless")
ADD_LEVEL_SHIFT_U8 = bytes(value ^ 128 for value in range(256))
COHORT = HERE / "native-ht-cohort.json"
SCOPE = "focused-direct-rust-3ht-2legacy"
SEED = 20261121
ITERATIONS = 3
WARMUPS = 2
MANIFEST = """[package]
name = "native-probe"
version = "0.0.0"
edition = "2024"
publish = false

[workspace]

[dependencies]
codec = { package = "jpeg2000-decoder", path = "../source", default-features = false }
"""


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def validate_options(baseline, candidate, pairs, arch):
    if not all(re.fullmatch(r"[0-9a-f]{40}", value) for value in (baseline, candidate)):
        raise ValueError("baseline/candidate must be exact 40-character lowercase commit IDs")
    if baseline == candidate:
        raise ValueError("baseline and candidate must differ")
    if not 2 <= pairs <= 24 or pairs % 2:
        raise ValueError("pairs must be even and between 2 and 24")
    if platform.system() != "Linux" or arch not in ARCH or platform.machine() != arch:
        raise ValueError("requires the selected native x86_64 or aarch64 Linux host")
    runner_arch = os.getenv("RUNNER_ARCH")
    if runner_arch and runner_arch != ARCH[arch][1]:
        raise ValueError(f"runner architecture mismatch: {runner_arch}")


def checked(command, prefix, *, cwd=None, env=None, seconds=120):
    if env is None:
        env = dict(os.environ, LC_ALL="C", GIT_NO_REPLACE_OBJECTS="1")
    metrics = measure(command, prefix, env=env, extended=True, cwd=cwd, timeout_s=seconds)
    if metrics["returncode"] != 0 or metrics["exit"] != 0:
        raise RuntimeError(f"command failed ({metrics['returncode']}): see {prefix}.*")
    return metrics


def text(prefix):
    return Path(str(prefix) + ".stdout").read_text().strip()


def clean_source(path, prefix, *, dependency=False):
    command = ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=all"]
    if dependency:
        command.append("--ignored")
    checked(command, prefix)
    if text(prefix):
        raise ValueError(f"dirty source: see {prefix}.stdout")


def require_upstream_commit(mirror, revision, prefix):
    git = ["git", "--git-dir", str(mirror)]
    checked([*git, "cat-file", "-t", revision], prefix / "object")
    if text(prefix / "object") != "commit":
        raise ValueError(f"not a commit: {revision}")
    checked([*git, "for-each-ref", "--format=%(refname)", "--contains", revision, "refs/heads/"],
            prefix / "upstream-branches")
    if not text(prefix / "upstream-branches"):
        raise ValueError(f"commit not reachable from an upstream branch: {revision}")


def sources(revisions, work, evidence):
    mirror = work / "upstream.git"
    # Exact SHA fetch alone may resolve objects in GitHub's shared fork network.
    # A fresh clone and upstream branch reachability avoid local/fork-only/PR refs.
    checked(["git", "clone", "--bare", "--no-tags", UPSTREAM + ".git", str(mirror)],
            evidence / "upstream-clone", seconds=600)
    for label, revision in revisions.items():
        require_upstream_commit(mirror, revision, evidence / label)
    for label, revision in revisions.items():
        source = work / label / "source"
        source.parent.mkdir()
        git = ["git", "--git-dir", str(mirror)]
        checked([*git, "worktree", "add", "--detach", str(source), revision],
                evidence / label / "checkout")
        clean_source(source, evidence / label / "source-before", dependency=True)
        checked(["git", "-C", str(source), "rev-parse", "HEAD", "HEAD^{tree}"],
                evidence / label / "revision")
        commit, tree = text(evidence / label / "revision").splitlines()
        if commit != revision:
            raise ValueError("checked out a different revision")
        write_json(evidence / label / "source.json", {
            "repository": UPSTREAM, "commit": commit, "tree": tree,
            "cargo_toml_sha256": sha((source / "Cargo.toml").read_bytes()),
            "source_cargo_lock_sha256": sha((source / "Cargo.lock").read_bytes()),
        })


def checked_bytes(data, fixture):
    if len(data) != fixture["bytes"] or sha(data) != fixture["sha256"]:
        raise ValueError(f"corrupt or changed input: {fixture['id']}")
    return data


def fixtures(output):
    ht = json.loads(COHORT.read_text())
    legacy_path = HERE / "cohort-v1.json"
    provenance = json.loads((HERE / "frozen-provenance.json").read_text())
    if sha(legacy_path.read_bytes()) != provenance["canonical_manifest_sha256"]:
        raise ValueError("legacy manifest differs from frozen provenance")
    legacy = {row["id"]: row for row in json.loads(legacy_path.read_text())["fixtures"]}
    selected = []
    for row in ht["fixtures"]:
        name = row["id"]
        record = dict(row, group="ht-target")
        selected.append((record, checked_bytes((HERE / "native-ht" / f"{name}.j2k").read_bytes(), record)))
    for name in LEGACY:
        boxed = checked_bytes((HERE / "frozen" / f"{name}.jp2").read_bytes(), legacy[name + "-jp2"])
        row = dict(legacy[name + "-j2k"], group="legacy-control", lossless=True)
        selected.append((row, checked_bytes(jp2_parts(boxed)[0], row)))
    result = []
    for row, data in selected:
        path = output / f"{row['id']}.j2k"
        path.write_bytes(data)
        result.append(dict(row, path=path.name))
    write_json(output / "fixture-manifest.json", {
        "scope": SCOPE, "api": "decode_codestream_reconstructed",
        "ht_provenance": ht, "ht_manifest_sha256": sha(COHORT.read_bytes()),
        "legacy_provenance": provenance, "fixtures": result,
    })
    return result


def native_signature(data, fixture):
    """Check all geometry, representation and length; return hashes over every native bit."""
    width, height, count = (fixture[key] for key in ("width", "height", "channels"))
    pixels = width * height
    expected_size = 8 * (6 + count * (10 + pixels))
    if len(data) != expected_size or struct.unpack_from("<6Q", data) != (1, width, height, 0, 0, count):
        raise ValueError("invalid native image header or byte count")
    offset = 48
    planes = []
    for _ in range(count):
        expected = (width, height, 8, 0, 1, 1, 0, 0, 0 if fixture["lossless"] else 16, pixels)
        if struct.unpack_from("<10Q", data, offset) != expected:
            raise ValueError("invalid native component geometry, type, precision or sample count")
        offset += 80
        samples = data[offset:offset + 8 * pixels]
        if samples == samples[:8] * pixels:
            raise ValueError("constant/blank native component")
        if fixture["lossless"]:
            # Reconstructed planes precede the unsigned level shift; only the
            # separate source-recovery check maps centered i64 values to u8.
            low = samples[::8]
            sign_extension = low.translate(bytes(128) + b"\xff" * 128)
            if any(samples[index::8] != sign_extension for index in range(1, 8)):
                raise ValueError("native lossless samples outside centered 8-bit range")
            planes.append(low.translate(ADD_LEVEL_SHIFT_U8))
        elif not any(sample < (127 << 16) - (1 << 15) for (sample,) in struct.iter_unpack("<q", samples)):
            raise ValueError("all-white component after rounding/clipping Q16 samples")
        offset += 8 * pixels
    if planes:
        interleaved = bytearray(count * pixels)
        for channel, plane in enumerate(planes):
            interleaved[channel::count] = plane
        if sha(interleaved) != fixture["source_samples_sha256"]:
            raise ValueError("native lossless output differs from first-party source samples")
    fingerprint = 14695981039346656037
    for (word,) in struct.iter_unpack("<Q", data):
        fingerprint = ((fingerprint ^ word) * 1099511628211) & ((1 << 64) - 1)
    return {"native_sha256": sha(data), "native_bytes": len(data), "fingerprint": f"{fingerprint:016x}"}


def qualify(dumps, fixture):
    signatures = {label: native_signature(dumps[label], fixture) for label in BACKENDS}
    if dumps["baseline"] != dumps["candidate"]:
        raise ValueError(f"{fixture['id']}: native baseline/candidate output differs")
    return dict(signatures["baseline"], fixture=fixture["id"], status="accepted-bit-exact")


def timings(stdout, signature):
    lines = stdout.splitlines()
    if (len(lines) != 1 + ITERATIONS or lines[0] != "ACCEPTED\t" + signature["fingerprint"]
            or any(not re.fullmatch(r"SAMPLE\t[1-9][0-9]*", line) for line in lines[1:])):
        raise ValueError("timed process refused, changed output, or emitted malformed samples")
    return [int(line.split("\t")[1]) for line in lines[1:]]


def native_profile(args):
    flags = {}
    for index, arg in enumerate(args):
        if arg == "--target" or arg.startswith("--target="):
            return False
        if arg.startswith("-C"):
            value = args[index + 1] if arg == "-C" else arg[2:]
            key, _, setting = value.partition("=")
            flags[key] = setting
    return (all(flags.get(key) == value for key, value in {
        "opt-level": "3", "lto": "thin", "codegen-units": "1", "target-cpu": "native",
    }.items()) and all(flags.get(key, "off") == "off" for key in ("debug-assertions", "overflow-checks")))


def build(label, work, evidence, arch):
    package = work / label / "probe"
    package.mkdir()
    (package / "Cargo.toml").write_text(MANIFEST)
    (package / "src").mkdir()
    shutil.copyfile(HERE / "native_probe.rs", package / "src/main.rs")
    prefix = evidence / label
    env = configuration_environment("combined", package / "target", prefix / "compiler")
    # Don't inherit target/allocator/profile overrides or user Cargo configuration.
    env = {key: value for key, value in env.items()
           if key in {"PATH", "HOME", "RUSTUP_HOME", "RUSTC_WRAPPER", "RUSTFLAGS",
                      "CONSUMER_INVOCATIONS", "CONSUMER_REAL_LINKER", "CARGO_TARGET_DIR",
                      "CARGO_BUILD_JOBS"} or key.startswith("CARGO_PROFILE_RELEASE_")}
    env.update(CARGO_HOME=str(package / "cargo-home"), CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS="false",
               CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS="false", LC_ALL="C", TMPDIR=str(work / "tmp"))
    lock = package / "Cargo.lock"
    # The final consumer graph is just this package and the no-default-features path crate.
    cargo = ["cargo", RUST]
    checked([*cargo, "generate-lockfile", "--offline"], prefix / "resolve", cwd=package, env=env)
    shutil.copyfile(lock, prefix / "Cargo.lock")
    write_json(prefix / "profile.json", {key: value for key, value in env.items()
                                         if key.startswith("CARGO_PROFILE_") or key == "RUSTFLAGS"})
    checked([*cargo, "build", "--release", "--locked", "--offline", "--verbose"],
            prefix / "build", cwd=package, env=env, seconds=1200)
    clean_source(work / label / "source", prefix / "source-after", dependency=True)
    final = []
    for path in (prefix / "compiler").glob("rustc-*.metrics.json"):
        args = json.loads(path.read_text())["command"]
        if "--crate-name" in args and args[args.index("--crate-name") + 1] == "native_probe":
            final.append(args)
    if len(final) != 1 or not native_profile(final[0]):
        raise ValueError(f"{label}: incorrect final compiler invocation")
    binary = package / "target/release/native-probe"
    data = binary.read_bytes()
    if data[:6] != b"\x7fELF\x02\x01" or struct.unpack_from("<H", data, 18)[0] != ARCH[arch][0]:
        raise ValueError(f"{label}: wrong final binary ELF architecture")
    write_json(prefix / "binary.json", {
        "path": str(binary), "sha256": sha(data), "bytes": len(data),
        "allocator": "std::alloc::System", "elf_machine": ARCH[arch][0],
        "argv": final[0], "harness_sha256": sha((package / "src/main.rs").read_bytes()),
        "consumer_toml_sha256": sha((package / "Cargo.toml").read_bytes()),
        "consumer_lock_sha256": sha(lock.read_bytes()),
    })
    return binary


def summarize(rows, cohort, pairs):
    result = []
    for fixture in cohort:
        selected = [row for row in rows if row["fixture"] == fixture["id"]]
        medians = {}
        absolute = {}
        for label in BACKENDS:
            processes = [row for row in selected if row["backend"] == label]
            if sorted(row["pair"] for row in processes) != list(range(pairs)):
                raise ValueError("missing or duplicate process pairs")
            values = sorted(t for row in processes for t in row["decode_ns"])
            medians[label] = {row["pair"]: statistics.median(row["decode_ns"]) for row in processes}
            absolute[label] = {
                "process_median_ns": statistics.median(medians[label].values()),
                "pooled_p95_ns": values[math.ceil(.95 * len(values)) - 1],
                "pooled_p99_ns": values[math.ceil(.99 * len(values)) - 1],
            }
        ratios = [medians["candidate"][pair] / medians["baseline"][pair] for pair in range(pairs)]
        result.append({"fixture": fixture["id"], "group": fixture["group"], "absolute": absolute,
                       "candidate_over_baseline": geometric(ratios),
                       "matched_pair_bootstrap95": interval(ratios), "pair_ratios": ratios})
    return result


def run(options):
    work = options.output.resolve()
    if not work.is_relative_to(ROOT / "target"):
        raise ValueError("use a fresh directory within this checkout's ignored target/")
    work.mkdir(parents=True, exist_ok=False)
    evidence = work / "evidence"
    evidence.mkdir()
    (work / "tmp").mkdir()
    validate_options(options.baseline, options.candidate, options.pairs, options.arch)
    clean_source(ROOT, evidence / "driver-status")
    checked(["git", "-C", str(ROOT), "remote", "get-url", "origin"], evidence / "driver-origin")
    if text(evidence / "driver-origin") not in {UPSTREAM, UPSTREAM + ".git"}:
        raise ValueError("driver checkout must come from the upstream repository")
    rust = capture(["rustc", RUST, "-vV"])
    if (rust["returncode"] or "release: 1.93.1" not in rust["stdout"].splitlines()
            or f"host: {options.arch}-unknown-linux-gnu" not in rust["stdout"].splitlines()):
        raise ValueError(f"expected pinned native Rust compiler: {rust}")
    cpus = sorted(os.sched_getaffinity(0))
    if not cpus:
        raise ValueError("no available CPU")
    pinned = ["/usr/bin/taskset", "-c", str(cpus[0])]
    revisions = dict(zip(BACKENDS, (options.baseline, options.candidate), strict=True))
    host = {"schema": 1, "scope": SCOPE, "mode": "qualification-only" if options.qualify_only else "paired",
            "revisions": revisions, "pairs": options.pairs, "case_shuffle_seed": SEED,
            "warmups": WARMUPS, "iterations": ITERATIONS, "arch": options.arch,
            "available_cpus": cpus, "binding": pinned, "platform": platform.platform(),
            "driver_head": capture(["git", "-C", str(ROOT), "rev-parse", "HEAD"]),
            "rustc": rust, "cargo": capture(["cargo", RUST, "-vV"]),
            "cc": capture(["cc", "--version"]), "lscpu": capture(["lscpu", "--json"]),
            "cpuinfo": Path("/proc/cpuinfo").read_text(),
            "rustc_native_cfg": capture(["rustc", RUST, "-Ctarget-cpu=native", "--print", "cfg"]),
            "hardware_counters": "unavailable (not collected)", "loadavg_start": os.getloadavg(),
            "run": {key: os.environ[key] for key in ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT",
                                                     "GITHUB_SHA", "ImageVersion") if key in os.environ}}
    write_json(evidence / "metadata.json", host)
    cohort = fixtures(evidence)
    sources(revisions, work, evidence)
    binaries = {label: build(label, work, evidence, options.arch) for label in BACKENDS}
    run_env = {key: value for key, value in os.environ.items() if key in {"PATH", "HOME"}}
    run_env["LC_ALL"] = "C"
    signatures = {}
    for fixture in cohort:
        name, path = fixture["id"], evidence / fixture["path"]
        dumps = {}
        for label in BACKENDS:
            checked_bytes(path.read_bytes(), fixture)
            prefix = evidence / "qualify" / name / label
            checked([*pinned, str(binaries[label]), "dump", str(path)], prefix, env=run_env)
            dumps[label] = Path(str(prefix) + ".stdout").read_bytes()
        signatures[name] = qualify(dumps, fixture)
        append(evidence / "qualification.jsonl", signatures[name])
    if options.qualify_only:
        return
    loadavg_start = os.getloadavg()
    rows = []
    rng = random.Random(SEED)
    for pair in range(options.pairs):
        order = cohort.copy()
        rng.shuffle(order)
        for case_index, fixture in enumerate(order):
            name, path = fixture["id"], evidence / fixture["path"]
            for position, label in enumerate(BACKENDS if pair % 2 == 0 else BACKENDS[::-1]):
                checked_bytes(path.read_bytes(), fixture)
                prefix = evidence / "processes" / f"pair-{pair:02d}" / name / label
                metrics = checked([*pinned, str(binaries[label]), "bench", str(path)], prefix, env=run_env)
                row = {"fixture": name, "input_sha256": fixture["sha256"], "backend": label,
                       "pair": pair, "case_index": case_index, "position": position, "metrics": metrics,
                       "decode_ns": timings(text(prefix), signatures[name])}
                append(evidence / "samples.jsonl", row)
                rows.append(row)
    write_json(evidence / "summary.json", {
        "schema": 1, "scope": SCOPE, "pairs": options.pairs,
        "qualification": list(signatures.values()), "loadavg_start": loadavg_start,
        "loadavg_end": os.getloadavg(),
        "ratios": "candidate / baseline; 4000 bootstrap draws of matched process pairs",
        "fixtures": summarize(rows, cohort, options.pairs),
    })


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", required=True)
    parser.add_argument("--candidate", required=True)
    parser.add_argument("--pairs", type=int, default=8)
    parser.add_argument("--arch", choices=ARCH, default=platform.machine())
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--validate-inputs", action="store_true")
    parser.add_argument("--qualify-only", action="store_true", help="build and qualify without latency sampling")
    args = parser.parse_args()
    try:
        if args.validate_inputs:
            validate_options(args.baseline, args.candidate, args.pairs, args.arch)
        else:
            run(args)
    except (OSError, RuntimeError, ValueError) as error:
        sys.exit(f"native comparison: {error}")
