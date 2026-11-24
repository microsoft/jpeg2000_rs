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
import native_palette
from run import append, capture, configuration_environment, sha as file_sha
from summarize import geometric, interval

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
UPSTREAM = "https://github.com/microsoft/jpeg2000_rs"
RUST = "1.93.1"
ARCH = {"x86_64": (62, "X64"), "aarch64": (183, "ARM64")}
BACKENDS = ("baseline", "candidate")
LEGACY = ("noisy-gray-lossless", "smooth-rgb-lossless")
ADD_LEVEL_SHIFT_U8 = bytes(value ^ 128 for value in range(256))
COHORT = HERE / "native-ht-cohort.json"
SCOPE = "focused-direct-rust-3ht-2legacy-2palette"
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
        record = dict(row, group="ht-target", format="j2k", api="decode_codestream_reconstructed")
        selected.append((record, checked_bytes((HERE / "native-ht" / f"{name}.j2k").read_bytes(), record)))
    for name in LEGACY:
        boxed = checked_bytes((HERE / "frozen" / f"{name}.jp2").read_bytes(), legacy[name + "-jp2"])
        row = dict(legacy[name + "-j2k"], group="legacy-control", lossless=True,
                   api="decode_codestream_reconstructed")
        selected.append((row, checked_bytes(jp2_parts(boxed)[0], row)))
    index = legacy[native_palette.SOURCE]
    selected.extend(native_palette.generate((HERE / "frozen" / index["path"]).read_bytes(), index))
    result = []
    for row, data in selected:
        path = output / f"{row['id']}.{row['format']}"
        path.write_bytes(data)
        result.append(dict(row, path=path.name))
    write_json(output / "fixture-manifest.json", {
        "scope": SCOPE,
        "ht_provenance": ht, "ht_manifest_sha256": sha(COHORT.read_bytes()),
        "legacy_provenance": provenance, "fixtures": result,
    })
    return result


def native_signature(data, fixture):
    """Check all geometry, representation and length; return hashes over every native bit."""
    if fixture.get("api") == "decode_jp2":
        expected = fixture["expected_native"]
        if len(data) != expected["native_bytes"] or sha(data) != expected["native_sha256"]:
            raise ValueError(f"{fixture['id']}: typed palette output differs from authored oracle")
        return signature(data)
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
    return signature(data)


def signature(data):
    fingerprint = 14695981039346656037
    for (word,) in struct.iter_unpack("<Q", data):
        fingerprint = ((fingerprint ^ word) * 1099511628211) & ((1 << 64) - 1)
    return {"native_sha256": sha(data), "native_bytes": len(data), "fingerprint": f"{fingerprint:016x}"}


def qualify(dumps, fixture):
    signatures = {label: native_signature(dumps[label], fixture) for label in BACKENDS}
    if dumps["baseline"] != dumps["candidate"]:
        raise ValueError(f"{fixture['id']}: native baseline/candidate output differs")
    api = fixture.get("api", "decode_codestream_reconstructed")
    return dict(signatures["baseline"], fixture=fixture["id"], status="accepted-bit-exact",
                api=api, oracle=("authored-palette" if api == "decode_jp2"
                                            else "raw-native"))


def timings(stdout, signature):
    lines = stdout.splitlines()
    if (len(lines) != 1 + ITERATIONS or lines[0] != "ACCEPTED\t" + signature["fingerprint"]
            or any(not re.fullmatch(r"SAMPLE\t[1-9][0-9]*", line) for line in lines[1:])):
        raise ValueError("timed process refused, changed output, or emitted malformed samples")
    return [int(line.split("\t")[1]) for line in lines[1:]]


def reject_cargo_configs(*directories, cargo_home=None):
    config_dirs = {cargo_home} if cargo_home is not None else set()
    for directory in directories:
        directory = directory.resolve()
        config_dirs.update(root / ".cargo" for root in (directory, *directory.parents))
    for directory in sorted(config_dirs):
        for name in ("config", "config.toml"):
            config = directory / name
            try:
                config.lstat()
            except FileNotFoundError:
                continue
            raise ValueError(f"Cargo configuration is not allowed in a comparison build: {config}")


def pinned_tool(tool, arch):
    resolution = capture(["rustup", "which", "--toolchain", RUST, tool])
    path = Path(resolution["stdout"].strip())
    if resolution["returncode"] or not path.is_absolute():
        raise ValueError(f"cannot resolve pinned {tool}: {resolution}")
    path = path.resolve(strict=True)
    digest = file_sha(path)
    version = capture([str(path), "-vV"])
    if (version["returncode"] or f"release: {RUST}" not in version["stdout"].splitlines()
            or f"host: {arch}-unknown-linux-gnu" not in version["stdout"].splitlines()
            or file_sha(path) != digest):
        raise ValueError(f"expected pinned native {tool}: {version}")
    return dict(version, sha256=digest)


def native_profile(args, *, dependency=False):
    flags = {}
    for index, arg in enumerate(args):
        if arg == "--target" or arg.startswith("--target="):
            return False
        if arg.startswith("-C"):
            value = args[index + 1] if arg == "-C" else arg[2:]
            key, _, setting = value.partition("=")
            flags[key] = setting
    if not all(flags.get(key) == value for key, value in {
        "opt-level": "3", "codegen-units": "1", "target-cpu": "native",
    }.items()) or not all(flags.get(key, "off") == "off" for key in ("debug-assertions", "overflow-checks")):
        return False
    # Cargo emits ThinLTO-ready bitcode for a dependency, and runs ThinLTO
    # at the final executable's link. Those use distinct rustc flags.
    if dependency:
        return flags.get("linker-plugin-lto") == "" and "lto" not in flags
    return flags.get("lto") == "thin" and "linker-plugin-lto" not in flags


def qualified_compilations(invocations, rust):
    compiler = rust["command"][0]
    if file_sha(compiler) != rust["sha256"]:
        raise ValueError("rustc executable hash changed since preflight")
    expected = {"native_probe", "jpeg2000_decoder"}
    actual = {}
    for path in sorted(invocations.glob("rustc-*.metrics.json")):
        record = json.loads(path.read_text())
        args = record["command"]
        if args[0] != compiler:
            raise ValueError(f"unexpected rustc executable in {path}: {args[0]}")
        if "--crate-name" not in args:
            continue
        crate = args[args.index("--crate-name") + 1]
        if crate not in expected:  # Cargo also runs compiler capability queries.
            continue
        if (crate in actual or record["returncode"] != 0
                or not native_profile(args, dependency=crate == "jpeg2000_decoder")):
            raise ValueError(f"{crate}: unqualified compiler invocation or profile: {path}")
        actual[crate] = args
    if actual.keys() != expected:
        raise ValueError(f"missing actual compiler invocations: {sorted(expected - actual.keys())}")
    return actual


def build(label, work, evidence, arch, rust, cargo):
    package = work / label / "probe"
    package.mkdir()
    (package / "Cargo.toml").write_text(MANIFEST)
    (package / "src").mkdir()
    shutil.copyfile(HERE / "native_probe.rs", package / "src/main.rs")
    prefix = evidence / label
    source = work / label / "source"
    cargo_home = package / "cargo-home"
    cargo_home.mkdir()
    env = configuration_environment("combined", package / "target", prefix / "compiler")
    # Only the driver-selected flags and collector survive into the native build.
    env = {key: value for key, value in env.items()
           if key in {"PATH", "HOME", "RUSTC_WRAPPER", "RUSTFLAGS",
                      "CONSUMER_INVOCATIONS", "CONSUMER_REAL_LINKER", "CARGO_TARGET_DIR",
                      "CARGO_BUILD_JOBS"} or key.startswith("CARGO_PROFILE_RELEASE_")}
    env.update(CARGO_HOME=str(cargo_home), RUSTC=rust["command"][0],
               CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS="false",
               CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS="false", LC_ALL="C", TMPDIR=str(work / "tmp"))
    lock = package / "Cargo.lock"
    # Cargo discovers configs from its cwd upward, independently of CARGO_HOME.
    # Invoke it only from the generated consumer, never from either source checkout.
    reject_cargo_configs(package, source, cargo_home=cargo_home)
    cargo_cmd = [cargo["command"][0]]
    checked([*cargo_cmd, "generate-lockfile", "--offline"], prefix / "resolve", cwd=package, env=env)
    shutil.copyfile(lock, prefix / "Cargo.lock")
    write_json(prefix / "profile.json", {key: value for key, value in env.items()
                                         if key.startswith("CARGO_PROFILE_") or key in
                                         {"RUSTFLAGS", "RUSTC", "RUSTC_WRAPPER", "CARGO_HOME"}})
    reject_cargo_configs(package, source, cargo_home=cargo_home)
    checked([*cargo_cmd, "build", "--release", "--locked", "--offline", "--verbose"],
            prefix / "build", cwd=package, env=env, seconds=1200)
    reject_cargo_configs(package, source, cargo_home=cargo_home)
    clean_source(source, prefix / "source-after", dependency=True)
    actual = qualified_compilations(prefix / "compiler", rust)
    binary = package / "target/release/native-probe"
    data = binary.read_bytes()
    if data[:6] != b"\x7fELF\x02\x01" or struct.unpack_from("<H", data, 18)[0] != ARCH[arch][0]:
        raise ValueError(f"{label}: wrong final binary ELF architecture")
    write_json(prefix / "binary.json", {
        "path": str(binary), "sha256": sha(data), "bytes": len(data),
        "allocator": "std::alloc::System", "elf_machine": ARCH[arch][0],
        "argv": actual["native_probe"], "decoder_argv": actual["jpeg2000_decoder"],
        "rustc": rust, "harness_sha256": sha((package / "src/main.rs").read_bytes()),
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
    reject_cargo_configs(work)
    clean_source(ROOT, evidence / "driver-status")
    checked(["git", "-C", str(ROOT), "remote", "get-url", "origin"], evidence / "driver-origin")
    if text(evidence / "driver-origin") not in {UPSTREAM, UPSTREAM + ".git"}:
        raise ValueError("driver checkout must come from the upstream repository")
    rust = pinned_tool("rustc", options.arch)
    cargo = pinned_tool("cargo", options.arch)
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
            "rustc": rust, "cargo": cargo,
            "cc": capture(["cc", "--version"]), "lscpu": capture(["lscpu", "--json"]),
            "cpuinfo": Path("/proc/cpuinfo").read_text(),
            "rustc_native_cfg": capture([rust["command"][0], "-Ctarget-cpu=native", "--print", "cfg"]),
            "hardware_counters": "unavailable (not collected)", "loadavg_start": os.getloadavg(),
            "run": {key: os.environ[key] for key in ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT",
                                                     "GITHUB_SHA", "ImageVersion") if key in os.environ}}
    write_json(evidence / "metadata.json", host)
    cohort = fixtures(evidence)
    sources(revisions, work, evidence)
    binaries = {label: build(label, work, evidence, options.arch, rust, cargo) for label in BACKENDS}
    run_env = {key: value for key, value in os.environ.items() if key in {"PATH", "HOME"}}
    run_env["LC_ALL"] = "C"
    signatures = {}
    for fixture in cohort:
        name, path = fixture["id"], evidence / fixture["path"]
        operation = "dump-jp2" if fixture["api"] == "decode_jp2" else "dump"
        dumps = {}
        for label in BACKENDS:
            checked_bytes(path.read_bytes(), fixture)
            prefix = evidence / "qualify" / name / label
            checked([*pinned, str(binaries[label]), operation, str(path)], prefix, env=run_env)
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
            operation = "bench-jp2" if fixture["api"] == "decode_jp2" else "bench"
            for position, label in enumerate(BACKENDS if pair % 2 == 0 else BACKENDS[::-1]):
                checked_bytes(path.read_bytes(), fixture)
                prefix = evidence / "processes" / f"pair-{pair:02d}" / name / label
                metrics = checked([*pinned, str(binaries[label]), operation, str(path)], prefix, env=run_env)
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
