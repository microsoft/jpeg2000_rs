#!/usr/bin/env python3
"""Cold final-consumer builds and paired, opposite-order native decode processes."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys

from measure import measure

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CONFIGS = {
    "generic": ("", "false", "16"),
    "cpu": ("-Ctarget-cpu=native", "false", "16"),
    "thinlto": ("", "thin", "16"),
    "cgu1": ("", "false", "1"),
    "combined": ("-Ctarget-cpu=native", "thin", "1"),
}
BACKENDS = ["current", "release022", "hayro-scalar"]
ARCHIVE_SHA256 = "9174c2cd54f8ba9401d48f3a71bc162dd999eacf7409662bc3339ddbe7d8cbcc"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def capture(command, *, env=None):
    result = subprocess.run(command, capture_output=True, text=True, env=env)
    return {"command": list(map(str, command)), "returncode": result.returncode,
            "stdout": result.stdout, "stderr": result.stderr}


def append(path, record):
    with path.open("a") as stream:
        stream.write(json.dumps(record, sort_keys=True) + "\n")
        stream.flush()
        os.fsync(stream.fileno())


def configuration_environment(config, directory, invocations):
    cpu, lto, cgu = CONFIGS[config]
    env = os.environ.copy()
    for key in list(env):
        if key.startswith("CARGO_PROFILE_") or key in {
            "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER",
            "RUSTC_WORKSPACE_WRAPPER", "CARGO_BUILD_RUSTFLAGS",
        }:
            del env[key]
    env.update({
        "CARGO_TARGET_DIR": str(directory),
        "CARGO_PROFILE_RELEASE_OPT_LEVEL": "3",
        "CARGO_PROFILE_RELEASE_LTO": lto,
        "CARGO_PROFILE_RELEASE_CODEGEN_UNITS": cgu,
        "CARGO_PROFILE_RELEASE_DEBUG": "0",
        "CARGO_PROFILE_RELEASE_STRIP": "none",
        "CARGO_PROFILE_RELEASE_PANIC": "unwind",
        "CARGO_PROFILE_RELEASE_INCREMENTAL": "false",
        "CARGO_BUILD_JOBS": "2",
        "RUSTC_WRAPPER": str(HERE / "compiler_wrapper.py"),
        "CONSUMER_INVOCATIONS": str(invocations),
        "CONSUMER_REAL_LINKER": shutil.which("cc") or "/usr/bin/cc",
        "RUSTFLAGS": (cpu + " -Clinker=" + str(HERE / "linker.py")).strip(),
    })
    return env


def compiler_evidence(invocations, config):
    final = []
    for path in invocations.glob("rustc-*.metrics.json"):
        record = json.loads(path.read_text())
        arguments = record["command"]
        if "--crate-name" in arguments:
            crate = arguments[arguments.index("--crate-name") + 1]
            if crate == "jpeg2000_final_consumer_bench":
                final.append(record)
    if len(final) != 1:
        raise ValueError(f"expected one actual final binary rustc invocation, got {len(final)}")
    flags = " ".join(final[0]["command"])
    cpu, lto, cgu = CONFIGS[config]
    required = ["opt-level=3", f"codegen-units={cgu}"]
    if cpu:
        required.append("target-cpu=native")
    elif "target-cpu=" in flags:
        raise ValueError("unexpected host-specific CPU policy")
    if lto == "thin":
        required.append("lto=thin")
    elif "lto=thin" in flags:
        raise ValueError("unexpected cross-crate ThinLTO")
    if not all(flag in flags for flag in required):
        raise ValueError(f"final rustc flags did not match {config}: {flags}")
    return final[0]


def source_evidence(output):
    result = capture(["cargo", "+1.93.1", "metadata", "--locked", "--offline",
                      "--manifest-path", str(HERE / "Cargo.toml"),
                      "--all-features", "--format-version", "1"])
    (output / "cargo-metadata.json").write_text(json.dumps(result, indent=2) + "\n")
    if result["returncode"]:
        raise ValueError("cargo metadata failed")
    source_trees = {}
    for package in json.loads(result["stdout"])["packages"]:
        if package["name"] != "jpeg2000-decoder":
            continue
        root = Path(package["manifest_path"]).parent
        source_trees[package["version"]] = {
            str(path.relative_to(root)): sha(path)
            for directory in ["src", "specs", "proofs"]
            for path in sorted((root / directory).rglob("*")) if path.is_file()
        }
    if source_trees.get("0.3.0") != source_trees.get("0.2.2") or len(source_trees) != 2:
        raise ValueError("main/release source controls are no longer identical")
    (output / "source-trees.json").write_text(json.dumps(source_trees, indent=2) + "\n")


def check_outcome(backend, fixture, outcome):
    expected = fixture.get("expected_lossless_samples_sha256")
    # Hayro is a performance comparator, never a pixel oracle. Its own output
    # must pass source recovery and shape checks before a ratio is eligible.
    if expected and outcome.get("samples_sha256_u8_interleaved") != expected:
        raise ValueError(f"{backend}: lossless source mismatch for {fixture['id']}")
    if fixture["group"] == "generated-1024":
        for key in ["width", "height", "channels"]:
            if outcome.get(key) != fixture[key]:
                raise ValueError(f"{backend}: invalid generated shape/status: {outcome}")


def run(options):
    output = options.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    fixtures_path = options.fixtures.resolve()
    manifest = json.loads(fixtures_path.read_text())
    shutil.copyfile(fixtures_path, output / "fixture-manifest.json")
    fixtures = manifest["fixtures"]
    for fixture in fixtures:
        if sha(fixtures_path.parent / fixture["path"]) != fixture["sha256"]:
            raise ValueError(f"input changed: {fixture['id']}")
    if options.pairs < 2 or options.pairs % 2:
        raise ValueError("--pairs must be even and >=2 for reversed order")
    if options.build_rounds < 2 or options.build_rounds % 2:
        raise ValueError("--build-rounds must be even and >=2 for reversed build order")
    if platform.system() != "Linux" or platform.machine() not in {"x86_64", "aarch64"}:
        raise ValueError("use a native x86_64/aarch64 Linux host")
    version = capture(["rustc", "+1.93.1", "-vV"])
    if version["returncode"] or "release: 1.93.1\n" not in version["stdout"]:
        raise ValueError("pinned Rust unavailable")
    metadata = {
        "schema": 1, "rustc": version, "platform": platform.platform(),
        "machine": platform.machine(), "uname": capture(["uname", "-a"]),
        "lscpu": capture(["lscpu", "--json"]),
        "cpuinfo": Path("/proc/cpuinfo").read_text(),
        "meminfo": Path("/proc/meminfo").read_text(),
        "cgroup_cpu_max": Path("/sys/fs/cgroup/cpu.max").read_text()
        if Path("/sys/fs/cgroup/cpu.max").exists() else None,
        "cargo": capture(["cargo", "+1.93.1", "-vV"]),
        "linker": capture(["cc", "--version"]),
        "rustc_generic_cfg": capture(["rustc", "+1.93.1", "--print", "cfg"]),
        "rustc_native_cfg": capture(["rustc", "+1.93.1", "-Ctarget-cpu=native", "--print", "cfg"]),
        "rustc_target_cpus": capture(["rustc", "+1.93.1", "--print", "target-cpus"]),
        "source_commit": capture(["git", "-C", str(ROOT), "rev-parse", "HEAD"]),
        "source_status": capture(["git", "-C", str(ROOT), "status", "--porcelain"]),
        "lockfile_sha256": sha(HERE / "Cargo.lock"),
        "manifest_sha256": sha(fixtures_path), "configs": CONFIGS,
        "pairs": options.pairs, "build_rounds": options.build_rounds,
        "iterations_per_process": options.iterations,
        "environment_allowlist": {key: value for key, value in os.environ.items()
                                  if key in {"GITHUB_SHA", "GITHUB_REF", "GITHUB_RUN_ID",
                                             "GITHUB_RUN_ATTEMPT", "RUNNER_ARCH", "RUNNER_OS",
                                             "ImageOS", "ImageVersion"}},
        "coverage": {"generic_final_cargo_consumer": True, "zune_image_workspace": False,
                     "pdfium_workspace": False, "native_execution_no_emulation": True},
    }
    (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    shutil.copyfile(HERE / "Cargo.lock", output / "Cargo.lock")
    fetched = capture(["cargo", "+1.93.1", "fetch", "--locked", "--manifest-path", str(HERE / "Cargo.toml")])
    (output / "fetch.json").write_text(json.dumps(fetched, indent=2) + "\n")
    if fetched["returncode"]:
        raise RuntimeError("cargo fetch failed")
    cargo_home = Path(os.environ.get("CARGO_HOME", str(Path.home() / ".cargo")))
    archives = list((cargo_home / "registry/cache").glob("*/jpeg2000-decoder-0.2.2.crate"))
    if len(archives) != 1 or sha(archives[0]) != ARCHIVE_SHA256:
        raise ValueError("historical published 0.2.2 archive hash mismatch")
    (output / "release-archive.json").write_text(json.dumps({
        "version": "0.2.2", "sha256": sha(archives[0]),
        "source_anchor": "4989f9c680beeb7bad4fbfd441a93aa373d2ba4f",
    }, indent=2) + "\n")
    source_evidence(output)
    for backend in BACKENDS:
        graph = capture(["cargo", "+1.93.1", "tree", "--locked", "--manifest-path",
                         str(HERE / "Cargo.toml"), "--no-default-features", "--features",
                         backend, "-e", "features"])
        (output / f"features-{backend}.json").write_text(json.dumps(graph, indent=2) + "\n")
        if graph["returncode"] or (backend == "hayro-scalar" and
                                  any(word in graph["stdout"] for word in ["fearless_simd", 'feature "simd"', "moxcms", "image v"])):
            raise ValueError("invalid scalar dependency graph")
    binaries = {}
    combinations = [(config, backend) for config in CONFIGS for backend in BACKENDS]
    for build_round in range(options.build_rounds):
        ordered = combinations if build_round % 2 == 0 else list(reversed(combinations))
        for config, backend in ordered:
            label = f"build-{build_round}-{config}-{backend}"
            directory = output / label
            invocations = directory / "invocations"
            invocations.mkdir(parents=True)
            env = configuration_environment(config, directory / "target", invocations)
            metrics = measure(
                ["cargo", "+1.93.1", "build", "--release", "--locked", "--offline",
                 "--manifest-path", str(HERE / "Cargo.toml"), "--no-default-features",
                 "--features", backend, "-vv", "--timings"],
                directory / "cargo", env=env, sample_tree=True)
            append(output / "builds.jsonl", {"round": build_round, "config": config,
                                           "backend": backend, "metrics": metrics})
            if metrics["returncode"]:
                raise RuntimeError(f"build failed: {label}; inspect {directory}/cargo.stderr")
            final_compile = compiler_evidence(invocations, config)
            executable = directory / "target/release/jpeg2000-final-consumer-bench"
            binary_dir = output / "binaries"
            binary_dir.mkdir(exist_ok=True)
            binary = binary_dir / f"r{build_round}-{config}-{backend}"
            shutil.copyfile(executable, binary)
            binary.chmod(0o755)
            binaries[config, backend] = binary
            (directory / "binary.json").write_text(json.dumps({
                "sha256": sha(binary), "bytes": binary.stat().st_size,
                "final_rustc": final_compile,
                "size": capture(["size", "-A", str(binary)]),
                "elf": capture(["readelf", "-h", "-n", "-A", str(binary)]),
                "environment": {key: value for key, value in env.items()
                                if key.startswith(("CARGO_PROFILE_", "RUSTFLAGS", "CARGO_BUILD_"))},
            }, indent=2) + "\n")
            timings = directory / "target/cargo-timings"
            if timings.exists():
                shutil.copytree(timings, directory / "cargo-timings")
            shutil.rmtree(directory / "target")
            print(f"built {label}", flush=True)
    reference = {}
    config_reference = {}
    variants = {}
    qualification = {}
    for pair in range(options.pairs):
        tuned_configs = list(CONFIGS)[1:]
        if pair % 2:
            tuned_configs.reverse()
        backends = BACKENDS if pair % 2 == 0 else list(reversed(BACKENDS))
        ordered_fixtures = fixtures if pair % 2 == 0 else list(reversed(fixtures))
        for tuned in tuned_configs:
            for backend in backends:
                for fixture in ordered_fixtures:
                    order = ["generic", tuned] if pair % 2 == 0 else [tuned, "generic"]
                    for position, config in enumerate(order):
                        label = f"p{pair}-{tuned}-{backend}-{fixture['id']}-{position}"
                        prefix = output / "samples" / label
                        metrics = measure([binaries[config, backend],
                                           fixtures_path.parent / fixture["path"],
                                           str(options.iterations)], prefix)
                        record = {"pair": pair, "tuned": tuned, "position": position,
                                  "backend": backend, "config": config,
                                  "fixture": fixture["id"], "metrics": metrics}
                        if metrics["returncode"]:
                            record["process_failure"] = Path(str(prefix) + ".stderr").read_text()
                            append(output / "samples.jsonl", record)
                            raise RuntimeError(f"decode process failed: {label}")
                        result = json.loads(Path(str(prefix) + ".stdout").read_text())
                        record.update(result)
                        key = backend, fixture["id"]
                        config_key = backend, config, fixture["id"]
                        reference.setdefault(key, result["outcome"])
                        config_reference.setdefault(config_key, result["outcome"])
                        record["matches_backend_generic"] = reference[key] == result["outcome"]
                        record["same_config_stable"] = config_reference[config_key] == result["outcome"]
                        record["qualification_errors"] = []
                        try:
                            check_outcome(backend, fixture, result["outcome"])
                        except ValueError as error:
                            record["qualification_errors"].append(str(error))
                        canonical = json.dumps(result["outcome"], sort_keys=True)
                        variants.setdefault(config_key, {})[canonical] = result["outcome"]
                        qualified = (record["matches_backend_generic"] and record["same_config_stable"]
                                     and not record["qualification_errors"])
                        qualification[config_key] = qualification.get(config_key, True) and qualified
                        append(output / "samples.jsonl", record)
                        if result["input_sha256"] != fixture["sha256"]:
                            raise ValueError("binary read a different input")
                        if backend != "hayro-scalar" and not qualified:
                            raise ValueError(f"configuration changed acceptance/samples: {key}")
            print(f"completed pair {pair} tuning {tuned}", flush=True)
    controls = {}
    for fixture in fixtures:
        current = reference["current", fixture["id"]]
        historical = reference["release022", fixture["id"]]
        if current != historical:
            raise ValueError(f"release/main output mismatch: {fixture['id']}")
        hayro = reference["hayro-scalar", fixture["id"]]
        comparable = fixture["group"] == "generated-1024" and all(
            current.get(key) == hayro.get(key) for key in ["width", "height", "channels", "status"])
        controls[fixture["id"]] = {
            "current": current, "release022": historical, "hayro-scalar": hayro,
            "hayro_performance_ratio_eligible": comparable,
            "hayro_pixels_equal": current.get("samples_sha256_u8_interleaved")
            == hayro.get("samples_sha256_u8_interleaved") if comparable else None,
            "hayro_is_pixel_oracle": False,
            "by_configuration": {
                backend: {config: config_reference[backend, config, fixture["id"]]
                          for config in CONFIGS}
                for backend in BACKENDS
            },
            "qualification": {
                backend: {config: qualification[backend, config, fixture["id"]]
                          for config in CONFIGS}
                for backend in BACKENDS
            },
            "output_variants": {
                backend: {config: list(variants[backend, config, fixture["id"]].values())
                          for config in CONFIGS}
                for backend in BACKENDS
            },
        }
    (output / "outcomes.json").write_text(json.dumps(controls, indent=2) + "\n")
    subprocess.run([sys.executable, str(HERE / "summarize.py"), str(output)], check=True)
    (output / "COMPLETE").write_text("all builds, input hashes, acceptance and sample fingerprints verified\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path, default=ROOT / "target/consumer-tuning/fixtures/manifest.json")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--pairs", type=int, default=4)
    parser.add_argument("--iterations", type=int, default=1)
    parser.add_argument("--build-rounds", type=int, default=2)
    run(parser.parse_args())
