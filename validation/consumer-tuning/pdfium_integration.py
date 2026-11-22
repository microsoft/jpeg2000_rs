#!/usr/bin/env python3
"""Matched optimized PDFium direct-backend builds; Cargo profiles do not configure GN."""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import random
import shutil
import statistics
import subprocess

from measure import measure
from run import append, capture, sha

PDFIUM_PIN = "ec9185e7d6b973d453f2fe6bf1d9eb9a1eb9ebc3"
DEPOT_PIN = "96a7c1418eedaa6bea333a8941e8a0078681b4d0"
OLD_DECODER = "89a85673266d204937025399ee921286dbce9c12"
DECODER_PIN = "4989f9c680beeb7bad4fbfd441a93aa373d2ba4f"
COMMON_ARGS = (
    "is_debug=false pdf_is_standalone=true is_component_build=false "
    "pdf_enable_v8=false pdf_enable_xfa=false pdf_use_skia=false "
    "use_remoteexec=false enable_rust=true enable_rust_cxx=true"
)


def checked(command, **kwargs):
    subprocess.run(command, check=True, **kwargs)

def capture_commands(command, prefix):
    result = subprocess.run(command, capture_output=True)
    Path(str(prefix) + ".stdout.bin").write_bytes(result.stdout)
    Path(str(prefix) + ".stderr.bin").write_bytes(result.stderr)
    return {"command": command, "returncode": result.returncode,
            "stdout": result.stdout.decode("utf-8", errors="backslashreplace"),
            "stderr": result.stderr.decode("utf-8", errors="backslashreplace"),
            "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(),
            "stderr_sha256": hashlib.sha256(result.stderr).hexdigest()}


def replace_exact(text, before, after, count):
    if text.count(before) != count:
        raise ValueError(f"pinned source does not contain {count} copies of {before!r}")
    return text.replace(before, after)


def roll_bridge(text):
    if text.count(r'jP  \x0d\x0a\x87\x0a') != 1:
        raise ValueError("pinned bridge JP2 signature changed")
    text = replace_exact(text, "file.file_type.brand", "file.file_type().brand", 2)
    text = replace_exact(text, "file.header.color.method", "file.header().color.method()", 1)
    return replace_exact(text, "&file.header.color", "&file.header().color", 1)


def roll_source_list(text, sources):
    if not sources or "upstream/src/lib.rs" not in sources:
        raise ValueError("missing actual rolled decoder crate root")
    if any(not p.startswith("upstream/src/") or not p.endswith(".rs") or ".." in p for p in sources):
        raise ValueError("unexpected decoder source-list path")
    block = "sources = [\n" + "".join(f'    "{p}",\n' for p in sorted(sources)) + "  ]"
    changed, count = re.subn(r"sources\s*=\s*\[.*?\]", lambda _: block, text, flags=re.S)
    if count != 1:
        raise ValueError("pinned GN target must have exactly one source list")
    return changed


def environment(root):
    env = os.environ.copy()
    env["PATH"] = str(root / "depot_tools") + os.pathsep + env["PATH"]
    env["DEPOT_TOOLS_DIR"] = str(root / "depot_tools")
    env["DEPOT_TOOLS_UPDATE"] = "0"
    env["DEPOT_TOOLS_BOOTSTRAP_PYTHON3"] = "1"
    for key in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER"):
        env.pop(key, None)
    return env


def prepare(root):
    if shutil.disk_usage(root.parent).free < 12 * 1024**3:
        raise ValueError("fresh PDFium checkout/build needs at least12GiB; do not delete shared data")
    root.mkdir(parents=True, exist_ok=False)
    depot = root / "depot_tools"
    checked(["git", "init", str(depot)])
    checked(["git", "-C", str(depot), "remote", "add", "origin",
             "https://chromium.googlesource.com/chromium/tools/depot_tools.git"])
    checked(["git", "-C", str(depot), "fetch", "--depth", "1", "origin", DEPOT_PIN])
    checked(["git", "-C", str(depot), "switch", "--detach", "FETCH_HEAD"])
    pdfium = root / "pdfium"
    checked(["git", "init", str(pdfium)])
    checked(["git", "-C", str(pdfium), "remote", "add", "origin",
             "https://pdfium.googlesource.com/pdfium.git"])
    checked(["git", "-C", str(pdfium), "fetch", "--depth", "1", "origin",
             "refs/changes/90/164990/2"])
    checked(["git", "-C", str(pdfium), "switch", "--detach", "FETCH_HEAD"])
    if capture(["git", "-C", str(pdfium), "rev-parse", "HEAD"])["stdout"].strip() != PDFIUM_PIN:
        raise ValueError("Gerrit patch-set identity changed")
    deps = pdfium / "DEPS"
    deps.write_text(replace_exact(deps.read_text(), OLD_DECODER, DECODER_PIN, 1))
    (root / ".gclient").write_text(
        "solutions = [{'name': 'pdfium', 'url': 'https://pdfium.googlesource.com/pdfium.git', "
        "'managed': False, 'custom_vars': {'checkout_configuration': 'minimal', "
        "'checkout_rust': True, 'checkout_jpeg2000_decoder': True, "
        "'checkout_testing_corpus': True}}]\ntarget_os = ['linux']\n")
    env = environment(root)
    checked([str(depot / "ensure_bootstrap")], cwd=root, env=env)
    checked(["gclient", "sync", "--nohooks", "--shallow"], cwd=root, env=env)
    upstream = pdfium / "third_party/jpeg2000_decoder/upstream"
    if capture(["git", "-C", str(upstream), "rev-parse", "HEAD"])["stdout"].strip() != DECODER_PIN:
        raise ValueError("PDFium did not resolve the published0.2.2 source anchor")
    bridge = pdfium / "core/fxcodec/jpx/rust_jpx_ffi.rs"
    text = roll_bridge(bridge.read_text())
    text = replace_exact(text, "            return false;\n        }\n        let dest = &mut dest[..output_size];",
                         '            eprintln!("Rust JPX pixel layout rejected: {width}x{height} channels={channels} count={count} pitch={pitch} dest={} pixels={}", dest.len(), self.pixels.len());\n'
                         "            return false;\n        }\n        let dest = &mut dest[..output_size];", 1)
    bridge.write_text(text)
    logger = pdfium / "core/fxcodec/jpx/rust_jpx_decoder.cpp"
    text = replace_exact(logger.read_text(), "#if !defined(NDEBUG)\n", "", 1)
    logger.write_text(replace_exact(text, "          std::string(error).c_str());\n#endif",
                                    "          std::string(error).c_str());", 1))
    gn = pdfium / "third_party/jpeg2000_decoder/BUILD.gn"
    sources = [p.relative_to(upstream.parent).as_posix() for p in (upstream / "src").rglob("*.rs")]
    gn.write_text(roll_source_list(gn.read_text(), sources))
    metadata = pdfium / "third_party/jpeg2000_decoder/README.chromium"
    text = replace_exact(metadata.read_text(), "Version: 0.2.0", "Version: 0.2.2", 1)
    metadata.write_text(replace_exact(text, OLD_DECODER, DECODER_PIN, 1))
    checked(["gclient", "runhooks"], cwd=root, env=env)


def render(binary, input_pdf, directory, prefix, env):
    directory.mkdir(parents=True, exist_ok=True)
    target = directory / "input.pdf"
    if not target.exists():
        shutil.copyfile(input_pdf, target)
    if sha(target) != sha(input_pdf):
        raise ValueError("render input changed")
    for page in directory.glob("input.pdf.*.png"):
        page.unlink()
    metrics = measure([binary, "--png", target], prefix, env=env)
    pages = sorted(directory.glob("input.pdf.*.png"))
    return metrics, pages


def compare_cases(pdfium, output, binaries, env):
    output.mkdir(parents=True, exist_ok=False)
    cases = {"bug_304": pdfium / "testing/resources/pixel/bug_304.pdf",
             "action_123": pdfium / "testing/corpus/fx/action/123.pdf"}
    summaries = {}
    for name, path in cases.items():
        if not path.is_file():
            summaries[name] = {"qualified": False, "reason": "matched-checkout PDF input unavailable"}
            continue
        frames = {}
        for backend in binaries:
            metrics, pages = render(binaries[backend], path, output / "render" / name / backend,
                                    output / f"parity-{name}-{backend}", env)
            frames[backend] = {"metrics": metrics, "pages": pages}
        parity = all(v["metrics"]["returncode"] == 0 and v["pages"] for v in frames.values())
        parity = parity and len(frames["rust"]["pages"]) == len(frames["openjpeg"]["pages"])
        comparisons = []
        if parity:
            for control, candidate in zip(frames["openjpeg"]["pages"], frames["rust"]["pages"]):
                compared = capture([str(pdfium / "out/openjpeg/pdfium_diff"), str(control), str(candidate)])
                comparisons.append(compared)
                parity = parity and compared["returncode"] == 0
        record = {"qualified": parity, "input_sha256": sha(path), "pixel_comparisons": comparisons,
                  "output_hashes": {b: [sha(p) for p in f["pages"]] for b, f in frames.items()}}
        if not parity:
            record["reason"] = "acceptance/page-count/pixel parity failed; no timing comparison"
            summaries[name] = record
            continue
        times = {b: [] for b in binaries}
        for backend in binaries:
            for warm in range(3):
                metrics, _ = render(binaries[backend], path, output / "render" / name / backend,
                                    output / f"warm-{name}-{backend}-{warm}", env)
                if metrics["returncode"]:
                    raise ValueError("qualified PDF render failed during warmup")
        for pair in range(8):
            for backend in ("openjpeg", "rust") if pair % 2 == 0 else ("rust", "openjpeg"):
                metrics, pages = render(binaries[backend], path, output / "render" / name / backend,
                                       output / f"sample-{name}-{pair}-{backend}", env)
                if metrics["returncode"] or [sha(p) for p in pages] != record["output_hashes"][backend]:
                    raise ValueError("qualified render acceptance/pixels changed during timing")
                times[backend].append(metrics["wall_ns"])
                append(output / "samples.jsonl", {"case": name, "pair": pair,
                                                  "backend": backend, "metrics": metrics})
        record["timing"] = {b: {"median_ns": statistics.median(values),
                                "p90_ns": sorted(values)[math.ceil(0.9 * len(values)) - 1]}
                            for b, values in times.items()}
        ratios = [math.log(times["rust"][i] / times["openjpeg"][i]) for i in range(8)]
        rng = random.Random(449)
        draws = sorted(math.exp(statistics.mean(rng.choices(ratios, k=8))) for _ in range(5000))
        record["rust_time_over_openjpeg"] = {
            "paired_geomean": math.exp(statistics.mean(ratios)),
            "paired_bootstrap95": [draws[125], draws[4874]],
        }
        record["scope"] = "fresh PDFium process, warm filesystem cache; parse/decode/render/PNG output included"
        summaries[name] = record
    return summaries


def run(options):
    root, output = options.work_root.resolve(), options.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    pdfium = root / "pdfium"
    os.chdir(pdfium)
    env = environment(root)
    env["TZ"] = "America/Los_Angeles"
    metadata = {
        "pdfium_pin": PDFIUM_PIN, "depot_tools_pin": DEPOT_PIN, "decoder_pin": DECODER_PIN,
        "configuration": COMMON_ARGS, "profile_environment_is_not_gn": True,
        "platform": capture(["uname", "-a"]), "cpu": capture(["lscpu", "--json"]),
        "source_diff": capture(["git", "-C", str(pdfium), "diff", "--binary"]),
        "coverage": {"actual_pdfium_direct_backend": True, "cargo_substitute": False,
                     "v8": False, "xfa": False, "skia": False,
                     "recovery": "separate strict and bounded-recovery configurations"},
    }
    for directory, expected in ((pdfium, PDFIUM_PIN),
                                (root / "depot_tools", DEPOT_PIN),
                                (pdfium / "third_party/jpeg2000_decoder/upstream", DECODER_PIN)):
        actual = capture(["git", "-C", str(directory), "rev-parse", "HEAD"])
        if actual["returncode"] or actual["stdout"].strip() != expected:
            raise ValueError(f"prepared source pin changed: {directory}")
    (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    binaries, builds, test_results = {}, {}, []
    for backend in ("openjpeg", "rust", "rust-recovery"):
        build = pdfium / "out" / backend
        args = (COMMON_ARGS + " pdf_enable_rust_jpeg2000=" + ("false" if backend == "openjpeg" else "true")
                + " pdf_enable_rust_jpeg2000_pdf_recovery=" + ("true" if backend == "rust-recovery" else "false"))
        checked(["gn", "gen", str(build), "--args=" + args], cwd=pdfium, env=env)
        metrics = measure(["ninja", "-C", build, "-j", "2", "pdfium_test", "pdfium_diff"],
                          output / f"build-{backend}", env=env, sample_tree=True)
        builds[backend] = metrics
        if metrics["returncode"]:
            raise ValueError(f"PDFium {backend} build failed; inspect preserved build stderr")
        log = (build / ".ninja_log").read_text()
        (output / f"build-{backend}-ninja.log").write_text(log)
        links = {}
        for line in log.splitlines():
            fields = line.split("\t")
            if len(fields) >= 5 and fields[3] in {"pdfium_test", "pdfium_diff"}:
                links[fields[3]] = int(fields[1]) - int(fields[0])
        if set(links) != {"pdfium_test", "pdfium_diff"}:
            raise ValueError("actual final Ninja link durations unavailable")
        metrics["final_link_ninja_ms"] = links
        preserved = output / "binaries" / backend
        preserved.mkdir(parents=True)
        for target in ("pdfium_test", "pdfium_diff"):
            shutil.copyfile(build / target, preserved / target)
            (preserved / target).chmod(0o755)
        commands = capture_commands(["ninja", "-C", str(build), "-t", "commands", "pdfium_test"],
                                    output / f"commands-{backend}")
        (output / f"commands-{backend}.json").write_text(json.dumps(commands, indent=2) + "\n")
        if commands["returncode"]:
            raise ValueError("effective PDFium compiler/link commands unavailable")
        if backend.startswith("rust") and not any("rustc" in line and "jpeg2000_decoder" in line
                                        for line in commands["stdout"].splitlines()):
            raise ValueError("actual JPEG2000 Rust compile not present in Ninja commands")
        binary = build / "pdfium_test"
        binaries[backend] = binary
        (output / f"binary-{backend}.json").write_text(json.dumps({
            "sha256": sha(binary), "bytes": binary.stat().st_size,
            "sections": capture(["size", "-A", str(binary)]),
            "help": capture([str(binary), "--help"]),
        }, indent=2) + "\n")
        for suite, selected in (("pixel", "bug_304.pdf"), ("corpus", "fx/action/123.pdf")):
            result = measure(["vpython3", f"testing/tools/run_{suite}_tests.py",
                              "--build-dir=out/" + backend, "-j", "2", selected],
                             output / f"tests-{backend}-{suite}", env=env)
            test_results.append({"backend": backend, "suite": suite, "selection": selected,
                                 "metrics": result})
    summaries = {
        "strict": compare_cases(pdfium, output / "strict",
                                {"openjpeg": binaries["openjpeg"], "rust": binaries["rust"]}, env),
        "bounded_recovery": compare_cases(pdfium, output / "bounded-recovery",
                                         {"openjpeg": binaries["openjpeg"], "rust": binaries["rust-recovery"]}, env),
    }
    (output / "summary.json").write_text(json.dumps({
        "builds": builds, "pixel_and_corpus_tests": test_results, "cases": summaries,
        "coverage": metadata["coverage"],
        "note": "GN flags come from actual Ninja commands; Cargo profiles do not configure these builds. "
                "Unqualified pixel cases are not performance wins; golden expectations unchanged.",
    }, indent=2) + "\n")
    (output / "COMPLETE").write_text("matched PDFium builds and explicit parity/timing dispositions recorded\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    setup = commands.add_parser("prepare")
    setup.add_argument("--work-root", type=Path, required=True)
    bench = commands.add_parser("run")
    bench.add_argument("--work-root", type=Path, required=True)
    bench.add_argument("--output", type=Path, required=True)
    options = parser.parse_args()
    if options.command == "prepare":
        prepare(options.work_root.resolve())
    else:
        run(options)
