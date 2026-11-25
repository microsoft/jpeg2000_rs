#!/usr/bin/env python3
"""Reproduce a matched in-memory OpenJPEG comparison; generated evidence stays outside the package."""

import argparse
from array import array
import csv
import json
import math
import os
from pathlib import Path
import platform
import re
import resource
import shutil
import statistics
import struct
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "validation" / "consumer-tuning"))
from generate_fixtures import generate, sha  # noqa: E402

OPENJPEG = "6c4a29b00211eb0430fa0e5e890f1ce5c80f409f"


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def capture(command, prefix, env=None, *, maximum_address_space=None):
    prefix.parent.mkdir(parents=True, exist_ok=True)
    if prefix.with_suffix(".json").exists():
        raise FileExistsError(prefix)
    start = time.monotonic_ns()
    before_exec = None
    if maximum_address_space:
        def before_exec():
            resource.setrlimit(resource.RLIMIT_AS, (maximum_address_space, maximum_address_space))
    with prefix.with_suffix(".stdout").open("wb") as out, \
            prefix.with_suffix(".stderr").open("wb") as err:
        process = subprocess.Popen(list(map(str, command)), stdout=out, stderr=err, env=env,
                                   preexec_fn=before_exec)
        _, status, usage = os.wait4(process.pid, 0)
        process.returncode = os.waitstatus_to_exitcode(status)
    metrics = {
        "command": list(map(str, command)), "returncode": process.returncode,
        "wall_ns": time.monotonic_ns() - start, "max_rss_kib": usage.ru_maxrss,
        "user_s": usage.ru_utime, "system_s": usage.ru_stime,
        "minor_faults": usage.ru_minflt, "major_faults": usage.ru_majflt,
        "thread_environment": {key: (env if env is not None else os.environ).get(key)
                               for key in ("OPJ_NUM_THREADS", "BENCH_OPENJPEG_THREADS")},
        "maximum_address_space": maximum_address_space,
    }
    write_json(prefix.with_suffix(".json"), metrics)
    return prefix.with_suffix(".stdout").read_bytes(), metrics


def execute(command, prefix, env=None, *, maximum_address_space=None):
    output, metrics = capture(command, prefix, env, maximum_address_space=maximum_address_space)
    if metrics["returncode"]:
        raise RuntimeError(f"command failed ({metrics['returncode']}); see {prefix}.stderr")
    return output


def read_dump(data):
    if len(data) < 24 or len(data) % 8:
        raise ValueError("invalid native dump length")
    width, height, count = struct.unpack_from("<3Q", data)
    offset = 24
    planes = []
    for _ in range(count):
        if offset + 32 > len(data):
            raise ValueError("missing component descriptor")
        shape = struct.unpack_from("<4Q", data, offset)
        offset += 32
        w, h, precision, signed = shape
        size = 8 * w * h
        if not w or not h or not 1 <= precision <= 31 or signed > 1:
            raise ValueError("unsupported component shape/precision")
        if offset + size > len(data):
            raise ValueError("missing component samples")
        values = array("q" if signed else "Q")
        values.frombytes(data[offset:offset + size])
        if sys.byteorder != "little":
            values.byteswap()
        planes.append((shape, values))
        offset += size
    if not width or not height or not count or offset != len(data):
        raise ValueError("invalid image shape or trailing bytes")
    return (width, height), planes


def compare_dumps(left, right):
    left_shape, left_planes = read_dump(left)
    right_shape, right_planes = read_dump(right)
    if left_shape != right_shape or len(left_planes) != len(right_planes):
        raise ValueError("decoded image geometry differs")
    different = maximum = samples = 0
    for (a_shape, a), (b_shape, b) in zip(left_planes, right_planes):
        if a_shape != b_shape:
            raise ValueError("decoded component geometry/type differs")
        for x, y in zip(a, b):
            difference = abs(x - y)
            different += difference != 0
            maximum = max(maximum, difference)
        samples += len(a)
    return {"samples": samples, "differing_samples": different,
            "maximum_absolute_difference": maximum,
            "rust_sha256": sha(left), "openjpeg_sha256": sha(right)}


def check_source(data, case):
    shape, planes = read_dump(data)
    if shape != (case["width"], case["height"]) or len(planes) != case["channels"]:
        raise ValueError("output does not have the authored source geometry")
    precision = case.get("precision", 8)
    if not 1 <= precision <= 16:
        raise ValueError("source oracle supports unsigned precision 1-16 only")
    sample_bytes = (precision + 7) // 8
    interleaved = bytearray(case["width"] * case["height"] * case["channels"] * sample_bytes)
    for channel, (descriptor, values) in enumerate(planes):
        if descriptor != (case["width"], case["height"], precision, 0) or any(v >= 1 << precision for v in values):
            raise ValueError("output does not have the authored unsigned source type")
        encoded = values.tobytes()
        for byte in range(sample_bytes):
            offset = byte if sys.byteorder == "little" else 7 - byte
            interleaved[channel * sample_bytes + byte::case["channels"] * sample_bytes] = encoded[offset::8]
    expected = case.get("expected_lossless_samples_sha256") or case["source_samples_sha256"]
    if sha(interleaved) != expected:
        raise ValueError("decoded lossless samples differ from the authored source")


def prepare(output):
    corpus = output / "corpus"
    manifest = generate(None, corpus)
    cases = []
    for item in manifest["fixtures"]:
        if item["group"] == "generated-1024" and item["format"] == "j2k":
            cases.append(dict(item, path=str(corpus / item["path"]),
                              corpus_class="B" if item["coding"]["wavelet"] == "9/7" else "A",
                              lossless=item["expected_lossless_samples_sha256"] is not None))
    ht = json.loads((ROOT / "validation/consumer-tuning/native-ht-cohort.json").read_text())
    for item in ht["fixtures"]:
        path = ROOT / "validation/consumer-tuning/native-ht" / (item["id"] + ".j2k")
        if sha(path.read_bytes()) != item["sha256"]:
            raise ValueError(f"HT fixture changed: {path}")
        cases.append(dict(item, path=str(path), corpus_class="E"))
    return {
        "scope": "first-party synthetic A/B smoke and three HT cases; not full A-G",
        "license": "MIT; repository LICENSE", "ht_provenance": ht,
        "cases": cases,
    }


def load_corpus(path):
    path = path.resolve()
    document = json.loads(path.read_text())
    if document.get("schema") != 1 or not isinstance(document.get("cases"), list):
        raise ValueError("expected schema-1 corpus manifest with cases")
    cases, identifiers = [], set()
    for item in document["cases"]:
        case = dict(item)
        name = case["id"]
        if not re.fullmatch(r"[a-z0-9][a-z0-9_-]*", name) or name in identifiers:
            raise ValueError(f"invalid or duplicate case ID: {name}")
        identifiers.add(name)
        relative = Path(case["path"])
        source = (path.parent / relative).resolve()
        if relative.is_absolute() or not source.is_relative_to(path.parent):
            raise ValueError(f"input escapes corpus directory: {name}")
        if not re.fullmatch(r"[0-9a-f]{64}", case["sha256"]) or sha(source.read_bytes()) != case["sha256"]:
            raise ValueError(f"input hash differs: {name}")
        if case["corpus_class"] not in "ABCDEFG" or len(case["corpus_class"]) != 1:
            raise ValueError(f"invalid corpus class: {name}")
        if type(case["lossless"]) is not bool or any(
                type(case[key]) is not int or case[key] <= 0
                for key in ("width", "height", "channels")):
            raise ValueError(f"invalid case shape/transform: {name}")
        if not case.get("origin") or not case.get("license"):
            raise ValueError(f"missing source origin/license: {name}")
        if case["lossless"] and not re.fullmatch(r"[0-9a-f]{64}", case["source_samples_sha256"]):
            raise ValueError(f"missing independent lossless source hash: {name}")
        case["path"] = str(source)
        cases.append(case)
    if not cases:
        raise ValueError("empty corpus")
    return dict(document, cases=cases, source_manifest=str(path),
                source_manifest_sha256=sha(path.read_bytes()))


def make_consumer(directory, decoder_source):
    directory.mkdir()
    manifest = directory / "Cargo.toml"
    manifest.write_text(
        '[package]\nname="bench-vs-openjpeg"\nversion="0.0.0"\nedition="2024"\n'
        'rust-version="1.88.0"\npublish=false\n[workspace]\n[dependencies]\n'
        'jpeg2000-decoder={path=' + json.dumps(str(decoder_source.resolve())) +
        ',default-features=false}\n[[bin]]\nname="bench-vs-openjpeg"\npath=' +
        json.dumps(str(HERE / "src/main.rs")) + "\n")
    return manifest


def build(output, config, options, source):
    work = output / config
    work.mkdir()
    env = dict(os.environ, OPJ_NUM_THREADS="0", BENCH_OPENJPEG_THREADS="1")
    env.pop("RUSTFLAGS", None)
    env.pop("CARGO_ENCODED_RUSTFLAGS", None)
    for key in ("CARGO_PROFILE_RELEASE_LTO", "CARGO_PROFILE_RELEASE_CODEGEN_UNITS"):
        env.pop(key, None)
    cflags = "-O3 -DNDEBUG -g -ffp-contract=off"
    if config != "generic":
        env.update(CARGO_PROFILE_RELEASE_LTO="thin", CARGO_PROFILE_RELEASE_CODEGEN_UNITS="1")
    if config == "native":
        env["RUSTFLAGS"] = "-C target-cpu=native"
        cflags += " -mcpu=native" if platform.machine() == "aarch64" else " -march=native"
    elif config == "x86-64-v3":
        if platform.machine() != "x86_64":
            raise ValueError("x86-64-v3 requires a native x86-64 runner")
        env["RUSTFLAGS"] = "-C target-cpu=x86-64-v3"
        cflags += " -march=x86-64-v3"
    target = work / "cargo"
    env.update(CARGO_TARGET_DIR=str(target), CARGO_PROFILE_RELEASE_DEBUG="1")
    manifest = HERE / "Cargo.toml"
    decoder = options.decoder_source.resolve() if options.decoder_source else ROOT
    if options.decoder_source:
        manifest = make_consumer(work / "consumer", decoder)
        execute(["cargo", "generate-lockfile", "--manifest-path", manifest],
                work / "consumer-lock", env)
    execute(["cargo", "build", "--release", "--locked", "--jobs", "2", "-vv",
             "--manifest-path", manifest], work / "rust-build", env)
    cmake = ["cmake", "-S", source, "-B", work / "openjpeg",
             "-DCMAKE_BUILD_TYPE=Release", "-DBUILD_SHARED_LIBS=OFF",
             "-DBUILD_CODEC=OFF", "-DBUILD_TESTING=OFF", "-DBUILD_JPIP=OFF",
             "-DCMAKE_POLICY_VERSION_MINIMUM=3.5",
             f"-DCMAKE_C_FLAGS_RELEASE={cflags}"]
    if shutil.which("ninja"):
        cmake += ["-G", "Ninja", f"-DCMAKE_MAKE_PROGRAM={shutil.which('ninja')}"]
    for variable in ("AR", "RANLIB"):
        if variable in env:
            cmake += [f"-DCMAKE_{variable}={env[variable]}"]
    execute(cmake, work / "openjpeg-configure", env)
    execute(["cmake", "--build", work / "openjpeg", "--parallel", "2"],
            work / "openjpeg-build", env)
    native = work / "bench-openjpeg"
    command = [env.get("CC", "cc"), "-std=c11", *cflags.split(), "-Wall", "-Wextra", "-Werror",
               "-I", source / "src/lib/openjp2", "-I", work / "openjpeg/src/lib/openjp2",
               HERE / "openjpeg.c", work / "openjpeg/bin/libopenjp2.a",
               "-lm", "-pthread", "-o", native]
    execute(command, work / "c-driver-build", env)
    rust = target / "release/bench-vs-openjpeg"
    write_json(work / "build.json", {
        "configuration": config, "cflags": cflags, "rustflags": env.get("RUSTFLAGS", ""),
        "lto": env.get("CARGO_PROFILE_RELEASE_LTO", "Cargo default"),
        "codegen_units": env.get("CARGO_PROFILE_RELEASE_CODEGEN_UNITS", "Cargo default"),
        "rust_binary_sha256": sha(rust.read_bytes()), "c_binary_sha256": sha(native.read_bytes()),
        "allocator": "system libc", "output": "native Rust TypedImage planar 64-bit samples",
        "openjpeg_native_output": "planar signed 32-bit components",
        "decoder_commit": subprocess.check_output(
            ["git", "-C", decoder, "rev-parse", "HEAD"], text=True).strip(),
        "decoder_src_tree": subprocess.check_output(
            ["git", "-C", decoder, "rev-parse", "HEAD:src"], text=True).strip(),
    })
    return {"rust": rust, "openjpeg": native}, env


def summarize(rows, output):
    groups = {}
    for row in rows:
        key = tuple(row[name] for name in ("config", "case", "class", "backend", "mode"))
        groups.setdefault(key, []).append(row["ns"])
    summaries = []
    for (config, case, group, backend, mode), values in sorted(groups.items()):
        quartiles = statistics.quantiles(values, n=4, method="inclusive")
        summaries.append({
            "config": config, "case": case, "class": group, "backend": backend, "mode": mode,
            "n": len(values), "median_ms": statistics.median(values) / 1e6,
            "iqr_ms": (quartiles[2] - quartiles[0]) / 1e6,
        })
    with (output / "summary.csv").open("w") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(summaries[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(summaries)
    lines = ["# Matched in-memory smoke baseline", "",
             "Synthetic subset only; no complete A-G or cross-target qualification.", "",
             "| Configuration | Case | Class | Rust median (IQR), ms | OpenJPEG typed median (IQR), ms | Ratio |",
             "|---|---|---|---|---|---|"]
    ratios = {}
    for row in summaries:
        if row["backend"] != "rust" or row["mode"] != "typed":
            continue
        other = next(x for x in summaries if x["config"] == row["config"]
                     and x["case"] == row["case"] and x["backend"] == "openjpeg"
                     and x["mode"] == "typed")
        ratio = row["median_ms"] / other["median_ms"]
        ratios.setdefault((row["config"], row["class"]), []).append(ratio)
        lines.append(f"| {row['config']} | {row['case']} | {row['class']} | "
                     f"{row['median_ms']:.4f} ({row['iqr_ms']:.4f}) | "
                     f"{other['median_ms']:.4f} ({other['iqr_ms']:.4f}) | {ratio:.4f} |")
    lines += ["", "## Geometric means (synthetic subset, not complete corpus classes)", ""]
    for (config, group), values in sorted(ratios.items()):
        value = math.exp(statistics.mean(map(math.log, values)))
        lines.append(f"- {config}, {group}: {value:.4f} ({'below' if value < 1 else 'not below'} 1.0).")
    (output / "summary.md").write_text("\n".join(lines) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--openjpeg-source", type=Path)
    parser.add_argument("--configs", default="generic,consumer,native")
    parser.add_argument("--case", default=".")
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument("--rounds", type=int, default=2)
    parser.add_argument("--iterations", type=int, default=15)
    parser.add_argument("--minimum-ms", type=int, default=2000)
    parser.add_argument("--warmups", type=int, default=3)
    parser.add_argument("--reduce", type=int, default=0)
    parser.add_argument("--window", default="-", help="absolute x,y,width,height, or -")
    parser.add_argument("--reuse-builds", type=Path, help="reuse hash-checked builds from a completed baseline")
    parser.add_argument("--corpus-manifest", type=Path, help="hash-checked schema-1 external corpus")
    parser.add_argument("--decoder-source", type=Path, help="separate clean committed decoder source")
    parser.add_argument("--maximum-address-space", type=int, default=8 * 1024**3,
                        help="equal per-decoder OS address-space cap in bytes; zero disables")
    options = parser.parse_args()
    if options.rounds < 2 or options.iterations < 2 or options.minimum_ms < 0 or options.warmups < 0:
        parser.error("requires >=2 rounds, >=2 iterations, and nonnegative time/warmups")
    if options.cpu not in os.sched_getaffinity(0):
        parser.error("selected CPU is outside allowed affinity")
    if not 0 <= options.reduce <= 16:
        parser.error("reduce must be between zero and sixteen")
    if options.maximum_address_space < 0:
        parser.error("maximum address space must be nonnegative")
    if options.decoder_source:
        if options.reuse_builds:
            parser.error("cannot relabel reused binaries with --decoder-source")
        if subprocess.check_output(
                ["git", "-C", options.decoder_source, "status", "--porcelain"], text=True).strip():
            parser.error("decoder source must be clean and committed")
    configs = options.configs.split(",")
    if len(set(configs)) != len(configs) or not set(configs) <= {"generic", "consumer", "native", "x86-64-v3"}:
        parser.error("invalid or duplicate configuration")
    output = options.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    corpus = load_corpus(options.corpus_manifest) if options.corpus_manifest else prepare(output)
    qualified_request = corpus.get("qualification", {}).get("request")
    if qualified_request is not None and qualified_request != {"reduce": options.reduce, "window": options.window}:
        raise ValueError("request differs from the corpus qualification request")
    cases = [case for case in corpus["cases"] if re.search(options.case, case["id"])]
    if not cases:
        parser.error("case selector matched no fixtures")
    if options.reduce or options.window != "-":
        for case in cases:
            case["corpus_class"] = "F"
    write_json(output / "corpus.json", dict(
        corpus, cases=cases, request={"reduce": options.reduce, "window": options.window}))
    source = options.openjpeg_source
    if source is None:
        source = output / "openjpeg-source"
        execute(["git", "clone", "--depth", "1", "--branch", "v2.5.4",
                 "https://github.com/uclouvain/openjpeg.git", source], output / "openjpeg-clone")
    source = source.resolve()
    revision = subprocess.check_output(["git", "-C", source, "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(["git", "-C", source, "status", "--porcelain"], text=True).strip()
    if revision != OPENJPEG or dirty:
        raise ValueError("requires clean pinned OpenJPEG 2.5.4 source")
    decoder_tree = subprocess.check_output(
        ["git", "-C", options.decoder_source or ROOT, "rev-parse", "HEAD:src"],
        text=True).strip()
    if options.reuse_builds:
        original_environment = json.loads(
            (options.reuse_builds.resolve() / "environment.json").read_text())
        if original_environment["architecture"] != platform.machine():
            raise ValueError("reused binaries are not from this native architecture")
        decoder_tree = original_environment["decoder_src_tree"]
    write_json(output / "environment.json", {
        "argv": sys.argv, "architecture": platform.machine(), "platform": platform.platform(),
        "affinity": sorted(os.sched_getaffinity(0)), "cpu": options.cpu,
        "openjpeg_revision": revision,
        "rustc": subprocess.check_output(["rustc", "-vV"], text=True),
        "cc": subprocess.check_output([os.getenv("CC", "cc"), "--version"], text=True),
        "decoder_src_tree": decoder_tree,
        "timing": "decode through output creation; input read, destruction, dump and CSV excluded",
        "runner_sha256": sha(Path(__file__).read_bytes()),
        "maximum_address_space": options.maximum_address_space,
    })
    rows = []
    with (output / "raw.csv").open("w") as stream:
        writer = csv.DictWriter(stream, fieldnames=["config", "case", "class", "backend", "mode", "round", "sample", "ns"], lineterminator="\n")
        writer.writeheader()
        for config in configs:
            if options.reuse_builds:
                previous = options.reuse_builds.resolve()
                if not (previous / "COMPLETE.json").exists():
                    raise ValueError("cannot reuse an incomplete build matrix")
                metadata = json.loads((previous / config / "build.json").read_text())
                binaries = {"rust": previous / config / "cargo/release/bench-vs-openjpeg",
                            "openjpeg": previous / config / "bench-openjpeg"}
                if any(sha(path.read_bytes()) != metadata[key] for path, key in [
                        (binaries["rust"], "rust_binary_sha256"),
                        (binaries["openjpeg"], "c_binary_sha256")]):
                    raise ValueError("reused binary hash differs")
                env = dict(os.environ, OPJ_NUM_THREADS="0", BENCH_OPENJPEG_THREADS="1")
                (output / config).mkdir()
                write_json(output / config / "build-reference.json",
                           {"baseline": str(previous), "metadata": metadata})
            else:
                binaries, env = build(output, config, options, source)
            for case in cases:
                print(f"{config}/{case['id']}: preflight and paired timing", flush=True)
                work = output / config / case["id"]
                dump = {}
                for backend, binary in binaries.items():
                    dump[backend] = execute(
                        ["taskset", "-c", options.cpu, binary, case["path"], "dump",
                         options.reduce, options.window, "1", "0", "0"],
                        work / (backend + "-dump"), env,
                        maximum_address_space=options.maximum_address_space)
                comparison = compare_dumps(dump["rust"], dump["openjpeg"])
                write_json(work / "correctness.json", comparison)
                if case["lossless"] and comparison["differing_samples"]:
                    raise ValueError(f"lossless mismatch: {case['id']}")
                if case["lossless"] and options.reduce == 0 and options.window == "-":
                    check_source(dump["rust"], case)
                for round_index in range(options.rounds):
                    order = ["rust", "openjpeg"] if round_index % 2 == 0 else ["openjpeg", "rust"]
                    for backend in order:
                        modes = ["typed"] if backend == "rust" else ["typed", "native"]
                        for mode in modes:
                            prefix = work / f"{backend}-{mode}-r{round_index}"
                            raw = execute(["taskset", "-c", options.cpu, binaries[backend],
                                           case["path"], mode, options.reduce, options.window, options.iterations,
                                           options.minimum_ms, options.warmups], prefix, env,
                                          maximum_address_space=options.maximum_address_space)
                            values = []
                            for line in raw.decode("ascii").splitlines():
                                tag, value = line.split("\t")
                                if tag != "SAMPLE" or int(value) <= 0:
                                    raise ValueError("invalid timing record")
                                values.append(int(value))
                            if len(values) < options.iterations or sum(values) < options.minimum_ms * 1_000_000:
                                raise ValueError("incomplete timing run")
                            for index, value in enumerate(values):
                                row = dict(config=config, case=case["id"], **{"class": case["corpus_class"]},
                                           backend=backend, mode=mode, round=round_index, sample=index, ns=value)
                                rows.append(row)
                                writer.writerow(row)
                            stream.flush()
    summarize(rows, output)
    write_json(output / "COMPLETE.json", {"records": len(rows), "cases": len(cases), "configurations": configs})


if __name__ == "__main__":
    main()
