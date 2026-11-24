#!/usr/bin/env python3
"""Focused public CAPI comparison, not a PDFium or external-corpus benchmark."""

import argparse
import json
import math
import os
from pathlib import Path
import platform
import random
import re
import shlex
import shutil
import statistics
import struct
import sys

import native_comparison as native
from generate_fixtures import samples, sha
from run import append, capture, configuration_environment, sha as file_sha
from summarize import geometric, interval

HERE, ROOT = native.HERE, native.ROOT
BACKENDS = (*native.BACKENDS, "openjpeg")
BASELINE = "9279e2bad720511c2187a3602eda361ebf037287"
CANDIDATE = "e0c2d4bfd299f31b51430c4a052ec720dad4a9d8"
OPENJPEG = "6c4a29b00211eb0430fa0e5e890f1ce5c80f409f"
SCOPE = "focused-public-capi-openjpeg-2.5.4"
CFLAGS = ("-O3", "-march=native", "-flto=thin", "-DNDEBUG")
WARMUPS, ITERATIONS = 2, 16
CASES = {
    "ht-gray8-lossless": None,
    "ht-large-rgb": None,
    "noisy-gray-lossless-j2k": None,
    "smooth-rgb-lossless-j2k": None,
    "ht-rgb8-lossy": "Blocked: no justified cross-library irreversible S32 criterion.",
    "palette-gray-alpha": "Blocked: no qualified cross-library palette/CDEF semantics.",
    "palette-mixed38": "Blocked: authored 38-bit palette exceeds Root's public CAPI precision limit.",
}


def tools(options, work, env):
    def identify(path, word):
        path = path.absolute()  # Keep driver basename (clang++, ld.lld).
        digest = file_sha(path)
        version = capture([str(path), "--version"], env=env)
        if version["returncode"] or not version["stdout"].startswith(word):
            raise ValueError(f"unexpected tool {path}: {version}")
        return dict(version, sha256=digest, resolved_path=str(path.resolve(strict=True)))

    found = {name: identify(options.llvm_bin / name, prefix) for name, prefix in
             (("clang", "clang version "), ("clang++", "clang version "),
              ("ld.lld", "LLD "), ("llvm-ar", "LLVM "))}
    ranlib = options.llvm_bin / "llvm-ranlib"
    if not ranlib.exists():
        # The Chromium LLVM bundle exposes this multicall binary only as llvm-ar.
        ranlib = work / "llvm-ranlib"
        ranlib.symlink_to((options.llvm_bin / "llvm-ar").resolve(strict=True))
    found["llvm-ranlib"] = identify(ranlib, "LLVM ")
    found["cmake"] = identify(options.cmake, "cmake version ")
    for name in ("rustc", "cargo"):
        found[name] = native.pinned_tool(name, options.arch, env=env)
    return found


def tool_path(tool):
    return tool["command"][0]


def require_tool(argv, tool):
    if argv[0] != tool_path(tool) or file_sha(argv[0]) != tool["sha256"]:
        raise ValueError(f"wrong actual compiler/tool: {argv[0]}")


def require_c_profile(argv, tool):
    require_tool(argv, tool)
    for pattern, expected in ((r"-O.*", "-O3"), (r"-m(?:arch|cpu)=.*", "-march=native"),
                              (r"-(?:f|fno-)lto.*", "-flto=thin"), (r"-[DU]NDEBUG.*", "-DNDEBUG")):
        flags = [arg for arg in argv[1:] if re.fullmatch(pattern, arg)]
        if not flags or set(flags) != {expected}:
            raise ValueError(f"unqualified native C/C++ profile: {argv}")
    if any(arg.startswith(("--target", "-target", "-Xclang", "@")) for arg in argv[1:]):
        raise ValueError(f"unexpected compiler override: {argv}")


def require_final_link(argv, toolchain):
    require_c_profile(argv, toolchain["clang++"])
    lld = toolchain["ld.lld"]
    require_tool([tool_path(lld)], lld)
    if ([arg for arg in argv if "lto-O" in arg] != ["-Wl,--lto-O3"]
            or [arg for arg in argv if arg.startswith(("--ld-path", "-fuse-ld"))]
            != ["--ld-path=" + tool_path(lld)]):
        raise ValueError("missing or overridden final LLD --lto-O3")


def without_depfile_flags(argv):
    # CMake's Makefiles add dependency tracking absent from compile_commands.json.
    args = iter(argv)
    result = []
    for arg in args:
        if arg in ("-MT", "-MF"):
            next(args)
        elif arg != "-MD":
            result.append(arg)
    return result


def source_receipt(source, revision, prefix, env):
    git = ["git", "-C", str(source)]
    native.checked([*git, "rev-parse", "HEAD", "HEAD^{tree}"], prefix / "source-revision", env=env)
    commit, tree = native.text(prefix / "source-revision").splitlines()
    if commit != revision:
        raise ValueError(f"unexpected source revision: {commit}, expected {revision}")
    archive = source.parent / "source.tar"
    native.checked([*git, "archive", "--format=tar", "-o", str(archive), commit],
                   prefix / "source-archive", env=env)
    native.write_json(prefix / "archive-source.json", {
        "commit": commit, "tree": tree, "source_tar_sha256": file_sha(archive),
    })


def build_root(label, work, evidence, toolchain, env):
    source, prefix = work / label / "source", evidence / label
    target, home = source.parent / "build", source.parent / "cargo-home"
    adapter = source / "adapters/openjpeg-capi"
    home.mkdir()
    native.reject_cargo_configs(source, adapter, cargo_home=home)
    rust, cargo = (toolchain[name] for name in ("rustc", "cargo"))
    config = configuration_environment("combined", target, prefix / "compiler")
    build_env = dict(env, **{k: config[k] for k in (
        "CARGO_TARGET_DIR", "CARGO_BUILD_JOBS", "RUSTC_WRAPPER", "CONSUMER_INVOCATIONS",
        "CARGO_PROFILE_RELEASE_OPT_LEVEL", "CARGO_PROFILE_RELEASE_CODEGEN_UNITS",
        "CARGO_PROFILE_RELEASE_DEBUG", "CARGO_PROFILE_RELEASE_INCREMENTAL",
    )})
    build_env.update(CARGO_HOME=str(home), RUSTC=tool_path(rust), CARGO_PROFILE_RELEASE_LTO="false",
                     CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS="false",
                     CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS="false",
                     RUSTFLAGS="-Ctarget-cpu=native -Cdebug-assertions=off "
                               "-Coverflow-checks=off -Clinker-plugin-lto")
    native.write_json(prefix / "build-env.json", build_env)
    cmd = [tool_path(cargo)]
    # Fetch only from the exact workspace lock into a private CARGO_HOME.
    native.checked([*cmd, "fetch", "--locked"], prefix / "fetch", cwd=source, env=build_env)
    native.reject_cargo_configs(source, adapter, cargo_home=home)
    native.checked([*cmd, "build", "--release", "--locked", "--offline", "--no-default-features",
                    "-p", "jpeg2000-openjpeg-compat", "--verbose"], prefix / "build",
                   cwd=source, env=build_env, seconds=1200)
    native.reject_cargo_configs(source, adapter, cargo_home=home)
    native.clean_source(source, prefix / "source-after", dependency=True, env=env)
    actual = native.qualified_compilations(prefix / "compiler", rust, capi=True)
    archive = target / "release/libjpeg2000_openjpeg_compat.a"
    native.write_json(prefix / "rust-profile.json", {
        "compiler": rust, "actual_compilations": actual, "archive_sha256": file_sha(archive),
        "shim_sha256": file_sha(adapter / "shim.c"),
    })
    return archive, adapter / "shim.c"


def build_openjpeg(work, evidence, toolchain, env, arch):
    source, build = work / "openjpeg/source", work / "openjpeg/build"
    prefix = evidence / "openjpeg"
    native.checked(["bash", str(HERE / "build-openjpeg254.sh"), "--source-only", str(source)],
                   prefix / "checkout", env=env)
    source_receipt(source, OPENJPEG, prefix, env)
    cmake, clang = (tool_path(toolchain[name]) for name in ("cmake", "clang"))
    build_env = dict(env, CONSUMER_INVOCATIONS=str(prefix / "compiler"))
    launcher = HERE / "compiler_wrapper.py"
    native.checked([cmake, "-S", source, "-B", build, "-G", "Unix Makefiles",
                    "-DCMAKE_BUILD_TYPE=Release", "-DCMAKE_EXPORT_COMPILE_COMMANDS=ON",
                    "-DCMAKE_POLICY_VERSION_MINIMUM=3.5", "-DBUILD_SHARED_LIBS=OFF",
                    "-DBUILD_CODEC=OFF", "-DBUILD_TESTING=OFF", "-DBUILD_JPIP=OFF",
                    "-DCMAKE_C_COMPILER=" + clang, "-DCMAKE_C_FLAGS_RELEASE=" + " ".join(CFLAGS),
                    "-DCMAKE_C_COMPILER_LAUNCHER=" + str(launcher) + ";--cc", "-DOPJ_USE_THREAD=ON",
                    "-DCMAKE_AR=" + tool_path(toolchain["llvm-ar"]),
                    "-DCMAKE_RANLIB=" + tool_path(toolchain["llvm-ranlib"]),
                    "-DCMAKE_EXE_LINKER_FLAGS=--ld-path=" + tool_path(toolchain["ld.lld"])],
                   prefix / "configure", env=build_env)
    native.checked([cmake, "--build", build, "--target", "openjp2", "--parallel", "2", "--verbose"],
                   prefix / "build", env=build_env, seconds=1200)
    recorded = []
    for p in sorted((prefix / "compiler").glob("cc-*.metrics.json")):
        record = json.loads(p.read_text())
        require_c_profile(record["command"], toolchain["clang"])
        if record["returncode"]:
            raise ValueError(f"failed OpenJPEG compilation: {p}")
        recorded.append(record["command"])
    database = json.loads((build / "compile_commands.json").read_text())
    expected = [shlex.split(row["command"]) for row in database]
    if not expected or sorted(expected) != sorted(map(without_depfile_flags, recorded)):
        raise ValueError("incomplete actual OpenJPEG compile commands")
    headers = source / "src/lib/openjp2"
    library = build / "src/lib/openjp2"
    archive = build / "bin/libopenjp2.a"
    if not archive.is_file():
        archive = library / "libopenjp2.a"
    macro = prefix / "native-macros"
    native.checked([clang, *CFLAGS, "-dM", "-E", "-x", "c", "/dev/null"], macro, env=env)
    neon = bool(re.search(r"^#define __ARM_NEON\b", native.text(macro), re.M))
    if neon != (arch == "aarch64"):
        raise ValueError("unexpected native NEON macro availability")
    neon_sources = [str(p.relative_to(source)) for p in sorted(headers.glob("*.[ch]"))
                    if re.search(r"arm_neon|__ARM_NEON|\bNEON\b", p.read_text(errors="replace"))]
    native.clean_source(source, prefix / "source-after", dependency=True, env=env)
    native.write_json(prefix / "library.json", {
        "compiler": toolchain["clang"], "archive": str(archive), "archive_sha256": file_sha(archive),
        "header_sha256": file_sha(headers / "openjpeg.h"),
        "config_sha256": file_sha(library / "opj_config.h"),
        "private_config_sha256": file_sha(library / "opj_config_private.h"),
        "neon_target_macro": neon, "upstream_neon_source_mentions": neon_sources,
        "actual_compilations": recorded,
    })
    return archive, headers, library


def link(label, work, prefix, archive, shim, includes, toolchain, env, arch):
    binary, source = work / label / "lifecycle", HERE / "matched_lifecycle.c"
    link_env = dict(env, CONSUMER_REAL_LINKER=tool_path(toolchain["clang++"]),
                    CONSUMER_INVOCATIONS=str(prefix / "final-link"))
    # Compile common C and optional shim as C; the real final driver is clang++.
    argv = [HERE / "linker.py", *CFLAGS, "-Wall", "-Wextra", "-Werror",
            *("-I" + str(path) for path in includes), "-x", "c", source]
    if shim is not None:
        argv.append(shim)
    native.checked([*argv, "-x", "none", archive, "--ld-path=" + tool_path(toolchain["ld.lld"]),
                    "-Wl,--lto-O3", "-Wl,-v", "-v", "-Wl,-Map," + str(prefix / "link.map"),
                    "-pthread", "-ldl", "-lm", "-o", binary], prefix / "link", env=link_env)
    receipt, = (prefix / "final-link").glob("link-*.metrics.json")
    actual = json.loads(receipt.read_text())
    require_final_link(actual["command"], toolchain)
    version = toolchain["ld.lld"]["stdout"].strip()
    stderr = (prefix / "link.stderr").read_text()
    if version not in native.text(prefix / "link") and version not in stderr:
        raise ValueError("final link did not report the selected LLD version")
    lld = tool_path(toolchain["ld.lld"])
    linker_argv = [shlex.split(line) for line in stderr.splitlines()
                   if line.lstrip().startswith(f'"{lld}"')]
    if len(linker_argv) != 1 or "--lto-O3" not in linker_argv[0] or str(archive) not in linker_argv[0]:
        raise ValueError("actual LLD subprocess did not link the selected archive at --lto-O3")
    # LLD 21 can use lto.tmp; newer LLD names ThinLTO outputs from their input.
    if not re.search(r"(?:lto\.tmp|/lifecycle\.lto\.)", (prefix / "link.map").read_text()):
        raise ValueError("final LLD map has no LTO objects")
    data = binary.read_bytes()
    if data[:6] != b"\x7fELF\x02\x01" or struct.unpack_from("<H", data, 18)[0] != native.ARCH[arch][0]:
        raise ValueError(f"{label}: wrong final ELF architecture")
    native.checked(["/usr/bin/ldd", binary], prefix / "libc", env=env)
    libc = re.search(r"libc\.so\.6 => (\S+)", native.text(prefix / "libc"))
    if not libc:
        raise ValueError("missing runtime libc")
    native.write_json(prefix / "binary.json", {
        "binary": str(binary), "sha256": sha(data), "archive_sha256": file_sha(archive),
        "harness_sha256": file_sha(source), "argv": actual["command"], "lld_argv": linker_argv[0],
        "allocator": "system libc", "libc_sha256": file_sha(libc[1]),
    })
    return binary, sha(data), file_sha(libc[1])


def snapshots(data):
    pos = 0

    def take(length):
        nonlocal pos
        chunk = data[pos:pos + length]
        if len(chunk) != length:
            raise ValueError("truncated CAPI snapshot")
        pos += length
        return chunk

    def words(n):
        return struct.unpack(f"<{n}I", take(4 * n))

    images = []
    for _ in range(2):
        present, = words(1)
        if present > 1:
            raise ValueError("invalid CAPI image presence")
        if not present:
            images.append(None)
            continue
        fields = words(8)
        icc = take(fields[6]) if fields[7] else b""
        planes = []
        for _ in range(fields[4]):
            plane = words(12)
            pixels = take(4 * plane[0] * plane[1]) if plane[-1] else b""
            planes.append((plane, pixels))
        images.append((fields, icc, planes))
    if pos != len(data):
        raise ValueError("trailing CAPI snapshot data")
    return images


def status(line):
    if not re.fullmatch(r"status [01] [01] [01](?: [0-9]+){7}", line):
        raise ValueError("missing or malformed CAPI status")
    return tuple(map(int, line.split()[1:]))


def check_shape(image, fixture, *, header):
    if image is None:
        raise ValueError("accepted CAPI image is missing")
    fields, icc, planes = image
    width, height, count = (fixture[k] for k in ("width", "height", "channels"))
    palette = fixture["id"] == "palette-gray-alpha"
    if palette and header:
        count = 1
    if fields[:5] != (0, 0, width, height, count) or fields[6:] != (0, 0) or icc:
        raise ValueError("unexpected CAPI image geometry/ICC metadata")
    for n, (plane, pixels) in enumerate(planes):
        alpha = int(palette and not header and n == 1)
        if plane[:10] != (width, height, 0, 0, 1, 1, 8, 0, 0, alpha) or plane[-1] != int(not header):
            raise ValueError("unexpected CAPI component metadata or sample presence")
        if not header and (any(pixels[i::4].strip(b"\0") for i in (1, 2, 3))
                           or pixels == pixels[:4] * (width * height)):
            raise ValueError("blank or out-of-range S32 plane")
    if header:
        return None
    interleaved = bytearray(width * height * count)
    for n, (_, pixels) in enumerate(planes):
        interleaved[n::count] = pixels[::4]
    return sha(interleaved)


def qualify(fixture, captures):
    name = fixture["id"]
    baseline, candidate, cpp = (captures[label] for label in BACKENDS)
    states = {label: status(captures[label][0]) for label in BACKENDS}
    if baseline != candidate:
        raise ValueError(f"{name}: Root status, callbacks, metadata or S32 output differs")
    outputs = {label: snapshots(captures[label][2]) for label in BACKENDS}
    result = {"fixture": name, "backends": {
        label: {"status": states[label], "status_line": captures[label][0],
                "callback_sha256": sha(captures[label][1]), "snapshot_sha256": sha(captures[label][2]),
                "image_metadata": [None if image is None else [image[0], [p[0] for p in image[2]]]
                                   for image in outputs[label]]}
        for label in BACKENDS}, "cpp_block_reason": CASES[name]}
    if name == "palette-mixed38":
        if states["baseline"][:6] != (1, 0, 0, 1, 0, 0) or b"Unsupported JPEG 2000 output plane" not in baseline[1]:
            raise ValueError(f"{name}: expected intentional Root precision refusal did not occur")
        if any(plane[-1] for image in outputs["baseline"] if image for plane, _ in image[2]):
            raise ValueError(f"{name}: refused image has output pixels")
        return dict(result, disposition="intentional-root-refusal-no-ratio")
    expected = fixture.get("source_samples_sha256") if fixture.get("lossless") else None
    if name == "palette-gray-alpha":
        indices = samples(1, False, size=fixture["width"])
        if sha(indices) != fixture["index_samples_sha256"]:
            raise ValueError("palette index source differs")
        interleaved = bytearray(2 * len(indices))
        interleaved[::2] = indices
        interleaved[1::2] = bytes(255 - i for i in indices)
        expected = sha(interleaved)
    labels = BACKENDS if CASES[name] is None else ("baseline",)
    for label in labels:
        if states[label][:5] != (1, 1, 1, 0, 0):
            raise ValueError(f"{name}: {label} refused or warned on an expected accepted case")
        header, image = outputs[label]
        check_shape(header, fixture, header=True)
        digest = check_shape(image, fixture, header=False)
        if expected is not None and digest != expected:
            raise ValueError(f"{name}: {label} differs from independent first-party samples")
    if CASES[name] is not None:
        return dict(result, disposition="root-exact-cpp-blocked-no-ratio", source_samples_sha256=expected)
    # Raw J2K has no declared colour space. Resolutions decoded and informative
    # callbacks are implementation metadata; retain both, never rewrite either.
    if [pixels for _, pixels in outputs["baseline"][1][2]] != [pixels for _, pixels in outputs["openjpeg"][1][2]]:
        raise ValueError(f"{name}: OpenJPEG output does not match Root S32 samples")
    return dict(result, disposition="exact-comparable", source_samples_sha256=expected)


def samples_from_child(stdout, expected):
    lines = stdout.splitlines()
    values = []
    for i in range(WARMUPS + ITERATIONS):
        if not lines or lines.pop(0) != expected:
            raise ValueError("timed child changed status or callbacks")
        if i >= WARMUPS:
            if not lines or not re.fullmatch(r"sample [1-9][0-9]*", lines[0]):
                raise ValueError("timed child omitted a latency")
            values.append(int(lines.pop(0).split()[1]))
    if lines:
        raise ValueError("unexpected timed child output")
    return values


def schedule(pair):
    # Reverse every adjacent pair of orders: every backend precedes each
    # other backend equally often, even when the round count is not a multiple of six.
    shift, reverse = (pair // 2) % len(BACKENDS), pair % 2
    order = BACKENDS[shift:] + BACKENDS[:shift]
    return order[::-1] if reverse else order


def summarize(rows, fixtures, pairs):
    groups = {}
    for row in rows:
        key = (row["fixture"], row["pair"], row["backend"])
        if key in groups:
            raise ValueError("duplicate timed process")
        groups[key] = row["decode_ns"]
    required = {(name, pair, label) for name in fixtures for pair in range(pairs) for label in BACKENDS}
    if set(groups) != required:
        raise ValueError("missing or extra timed processes")
    result = {}
    for name in fixtures:
        medians, absolute = {}, {}
        for label in BACKENDS:
            children = [groups[name, pair, label] for pair in range(pairs)]
            medians[label] = [statistics.median(child) for child in children]
            pool = sorted(t for child in children for t in child)
            absolute[label] = {"process_median_ns": statistics.median(medians[label]),
                               **{f"pooled_p{p}_ns": pool[math.ceil(len(pool) * p / 100) - 1]
                                  for p in (95, 99)}}
        ratios = {}
        for numerator, denominator in (("candidate", "baseline"), ("baseline", "openjpeg"),
                                       ("candidate", "openjpeg")):
            raw = [a / b for a, b in zip(medians[numerator], medians[denominator], strict=True)]
            ratios[numerator + "_over_" + denominator] = {
                "geomean": geometric(raw), "bootstrap95": interval(raw), "pairs": raw,
            }
        result[name] = {"absolute": absolute, "ratios": ratios}
    return result


def validate(options):
    native.validate_options(options.baseline, options.candidate, options.pairs, options.arch)
    if options.pairs not in (8, 24):
        raise ValueError("matched comparison requires 8 or 24 pairs")


def run(options):
    validate(options)
    work = options.output.resolve()
    if not work.is_relative_to(ROOT / "target") or work == ROOT / "target":
        raise ValueError("use a fresh directory within this checkout's ignored target/")
    native.reject_cargo_configs(work, ROOT)
    work.mkdir(parents=True)
    evidence = work / "evidence"
    evidence.mkdir()
    for name in ("tmp", "home"):
        (work / name).mkdir()
    rustup = Path(os.environ.get("RUSTUP_HOME", Path.home() / ".rustup")).resolve()
    rustup_bin = Path(shutil.which("rustup") or "rustup").resolve().parent
    env = {"PATH": f"/usr/bin:/bin:{rustup_bin}", "LC_ALL": "C", "HOME": str(work / "home"),
           "TMPDIR": str(work / "tmp"), "RUSTUP_HOME": str(rustup), "GIT_CONFIG_NOSYSTEM": "1",
           "GIT_NO_REPLACE_OBJECTS": "1", "OPJ_NUM_THREADS": "0"}
    native.clean_source(ROOT, evidence / "driver-status", env=env)
    native.checked(["git", "-C", ROOT, "remote", "get-url", "origin"], evidence / "driver-origin", env=env)
    if native.text(evidence / "driver-origin") not in {native.UPSTREAM, native.UPSTREAM + ".git"}:
        raise ValueError("driver checkout must come from the upstream repository")
    toolchain = tools(options, work, env)
    cpus = sorted(os.sched_getaffinity(0))
    if not cpus:
        raise ValueError("no available CPU")
    pinned = ["/usr/bin/taskset", "-c", str(cpus[0])]
    cohort = native.fixtures(evidence)
    if len(cohort) != len(CASES) or {row["id"] for row in cohort} != set(CASES):
        raise ValueError("changed seven-fixture cohort; dispositions must be reviewed")
    revisions = dict(zip(native.BACKENDS, (options.baseline, options.candidate), strict=True))
    native.write_json(evidence / "metadata.json", {
        "schema": 1, "scope": SCOPE, "revisions": dict(revisions, openjpeg=OPENJPEG),
        "driver_head": capture(["git", "-C", ROOT, "rev-parse", "HEAD"], env=env),
        "driver_argv": [sys.executable, *sys.argv],
        "mode": "qualification-only" if options.qualify_only else "paired", "arch": options.arch,
        "host": capture(["lscpu", "--json"], env=env), "binding": pinned, "toolchain": toolchain,
        "environment": env, "warmups": WARMUPS, "iterations": ITERATIONS, "pairs": options.pairs,
        "case_order_seed": native.SEED, "case_dispositions": CASES,
        "hardware_counters": "not collected",
    })
    native.sources(revisions, work, evidence, env=env)
    openjpeg, *includes = build_openjpeg(work, evidence, toolchain, env, options.arch)
    inputs = {"openjpeg": (openjpeg, None)}
    for label, revision in revisions.items():
        source_receipt(work / label / "source", revision, evidence / label, env)
        inputs[label] = build_root(label, work, evidence, toolchain, env)
    binaries = {label: link(label, work, evidence / label, *inputs[label], includes, toolchain, env, options.arch)
                for label in BACKENDS}
    if len({entry[2] for entry in binaries.values()}) != 1:
        raise ValueError("different runtime libc")

    def invocation(fixture, label, iterations):
        path = evidence / fixture["path"]
        native.checked_bytes(path.read_bytes(), fixture)
        binary, digest, _ = binaries[label]
        if file_sha(binary) != digest:
            raise ValueError(f"{label}: final binary changed")
        return [*pinned, binary, fixture["format"], path, str(iterations)]

    qualification, failures = {}, []
    for fixture in cohort:
        name = fixture["id"]
        captures = {}
        for label in BACKENDS:
            prefix = evidence / "qualify" / name / label
            dump = prefix.with_suffix(".s32")
            native.checked([*invocation(fixture, label, 0), dump], prefix, env=env)
            captures[label] = (native.text(prefix), prefix.with_suffix(".stderr").read_bytes(), dump.read_bytes())
        try:
            result = qualify(fixture, captures)
        except ValueError as error:
            failures.append(str(error))
            result = {"fixture": name, "disposition": "failed", "reason": str(error)}
        append(evidence / "qualification.jsonl", result)
        qualification[name] = result
    if failures:
        raise ValueError("; ".join(failures))
    comparable = [fixture for fixture in cohort if qualification[fixture["id"]]["disposition"] == "exact-comparable"]
    if not comparable or len(comparable) != sum(reason is None for reason in CASES.values()):
        raise ValueError("missing exact comparable fixtures")
    if options.qualify_only:
        return

    rows, rng = [], random.Random(native.SEED)
    load_start = os.getloadavg()
    for pair in range(options.pairs):
        order = comparable.copy()
        rng.shuffle(order)
        for case_index, fixture in enumerate(order):
            name = fixture["id"]
            for position, label in enumerate(schedule(pair)):
                prefix = evidence / "processes" / f"pair-{pair:02d}" / name / label
                metrics = native.checked(invocation(fixture, label, ITERATIONS), prefix, env=env)
                for key in ("user_s", "system_s", "max_process_rss_kib"):
                    if type(metrics.get(key)) not in (int, float) or not math.isfinite(metrics[key]) or metrics[key] < 0:
                        raise ValueError(f"missing or malformed GNU time field: {key}")
                if metrics["max_process_rss_kib"] == 0:
                    raise ValueError("GNU time reported no resident-set measurement")
                expected = qualification[name]["backends"][label]["status_line"]
                row = {"fixture": name, "input_sha256": fixture["sha256"], "binary_sha256": binaries[label][1],
                       "backend": label, "pair": pair, "case_index": case_index, "position": position,
                       "metrics": metrics, "decode_ns": samples_from_child(native.text(prefix), expected)}
                append(evidence / "samples.jsonl", row)
                rows.append(row)
    native.write_json(evidence / "summary.json", {
        "scope": SCOPE, "pairs": options.pairs, "qualification": qualification,
        "loadavg_start": load_start, "loadavg_end": os.getloadavg(),
        "uncertainty": "4000 bootstrap draws of matched fresh process pairs; per fixture only",
        "fixtures": summarize(rows, [row["id"] for row in comparable], options.pairs),
    })


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", default=BASELINE)
    parser.add_argument("--candidate", default=CANDIDATE)
    parser.add_argument("--arch", choices=native.ARCH, default=platform.machine())
    parser.add_argument("--pairs", type=int, default=8)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--llvm-bin", required=True, type=Path)
    parser.add_argument("--cmake", type=Path, default=Path("/usr/bin/cmake"))
    parser.add_argument("--validate-inputs", action="store_true")
    parser.add_argument("--qualify-only", action="store_true")
    options = parser.parse_args()
    try:
        validate(options) if options.validate_inputs else run(options)
    except (OSError, RuntimeError, ValueError) as error:
        sys.exit(f"matched CAPI comparison: {error}")
