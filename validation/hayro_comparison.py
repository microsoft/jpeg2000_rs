"""Pinned decoder comparison; output qualification precedes performance ratios."""

from __future__ import annotations

import hashlib
import json
import os
import platform
import shutil
import statistics
import struct
import subprocess
import tempfile
from functools import lru_cache
from pathlib import Path

from jsonschema import Draft202012Validator, ValidationError

import framework
import numerical
from resource_benchmarks import _peak_rss

HAYRO_VERSION = "0.4.1"
HAYRO_CHECKSUM = "122c5f834c37a2260b9c851bb8be685cf539b2a8b94b704a931ef7d2525d5835"
HAYRO_REVISION = "ea9c81dc70cde40c64205986fdcfcd481fe934d8"
MANIFEST = framework.VALIDATION / "compare" / "Cargo.toml"
SCHEMA = framework.VALIDATION / "hayro-comparison.schema.json"

PERFORMANCE_CASES = (
    (numerical.NumericalCase("perf-gray1024", width=1024, height=1024), False),
    (numerical.NumericalCase("perf-rgb512-jp2", width=512, height=512, channels=3, format="jp2"), False),
    (numerical.NumericalCase("perf-gray16-512", width=512, height=512, precision=16), False),
    (numerical.NumericalCase("perf-gray1024-lossy", width=1024, height=1024,
                            lossless=False, options=("-I", "-r", "1"),
                            maximum_error=1, maximum_rmse=0.25), False),
    (numerical.NumericalCase("perf-rgb512-lossy", width=512, height=512, channels=3,
                            lossless=False, options=("-I", "-r", "1"),
                            maximum_error=2, maximum_rmse=0.5), False),
    (numerical.NumericalCase("perf-tiles-origin", width=512, height=512,
                            options=("-t", "128,128", "-d", "3,5")), False),
    (numerical.NumericalCase("perf-ht-gray1024", width=1024, height=1024), True),
    (numerical.NumericalCase("perf-ht-rgb512", width=512, height=512, channels=3), True),
)


def _limits():
    if framework.resource is None:
        raise RuntimeError("POSIX comparison process limits are unavailable")
    framework.resource.setrlimit(framework.resource.RLIMIT_AS, (1 << 30, 1 << 30))
    framework.resource.setrlimit(framework.resource.RLIMIT_FSIZE, (64 << 20, 64 << 20))


def build_adapters():
    builds = {}
    for name, flags in (("default", []), ("scalar", ["--no-default-features", "--features", "scalar"])):
        target = framework.RESULTS_DIR / "comparison" / f"build-{name}"
        command = ["cargo", "build", "--release", "--locked", "--manifest-path", str(MANIFEST),
                   "--target-dir", str(target), *flags]
        subprocess.run(command, cwd=framework.ROOT, check=True)
        executable = target / "release" / "jpeg2000-comparison"
        if not executable.is_file():
            raise FileNotFoundError(f"comparison adapter not built: {executable}")
        builds[name] = {"path": str(executable), "sha256": framework.sha256_file(executable),
                        "hayro_features": "published-defaults" if name == "default" else "std-only",
                        "command": command}
    return builds


def canonical_digest(layout, values):
    digest = hashlib.sha256(b"jpeg2000-comparison-v1\0")
    digest.update(struct.pack("<III", layout["width"], layout["height"], len(layout["components"])))
    for component in layout["components"]:
        digest.update(struct.pack("<IIBB", component["width"], component["height"],
                                  component["precision"], int(component["signed"])))
    for value in values:
        digest.update(struct.pack("<q", value))
    return digest.hexdigest()

@lru_cache(maxsize=1)
def _observation_validator():
    schema = json.loads(SCHEMA.read_text())
    return Draft202012Validator({"$ref": "#/$defs/observation", "$defs": schema["$defs"]})


def validate_observation(observation):
    try:
        _observation_validator().validate(observation)
    except ValidationError as error:
        raise ValueError(f"invalid comparison adapter observation: {error.message}") from error


def read_observation(observation, samples_path, iterations):
    validate_observation(observation)
    if (observation.get("schema_version") != 1 or observation.get("hayro_version") != HAYRO_VERSION
            or observation.get("status") != "decoded" or observation.get("decoder_accepted") is not True):
        raise ValueError("comparison requires a successful decoded observation")
    layout = observation["layout"]
    components = layout["components"]
    if (not 1 <= len(components) <= 64 or type(layout["width"]) is not int
            or type(layout["height"]) is not int or layout["width"] <= 0 or layout["height"] <= 0):
        raise ValueError("comparison output layout is empty")
    count = sum(component["width"] * component["height"] for component in components)
    if count <= 0 or count > 16_777_216 or observation["sample_count"] != count:
        raise ValueError("comparison sample count is outside its declared layout/profile")
    if samples_path.stat().st_size != count * 8:
        raise ValueError("comparison sample-file size differs from its layout")
    values = [value for (value,) in struct.iter_unpack("<q", samples_path.read_bytes())]
    if canonical_digest(layout, values) != observation["output_sha256"]:
        raise ValueError("comparison output hash does not bind its samples/layout")
    timings = observation["timings"]
    if len(timings) != iterations:
        raise ValueError("comparison adapter did not measure the requested iterations")
    for timing in timings:
        decode, total = timing["decode_ns"], timing["common_output_ns"]
        if type(decode) is not int or type(total) is not int or not 0 < decode <= total:
            raise ValueError("comparison timing is missing, nonpositive or inconsistent")
    image = {"width": layout["width"], "height": layout["height"], "components": []}
    offset = 0
    for component in components:
        width, height, precision = component["width"], component["height"], component["precision"]
        if (type(width) is not int or type(height) is not int or type(precision) is not int
                or width <= 0 or height <= 0 or component["signed"] is not False or not 1 <= precision <= 16):
            raise ValueError("comparison output exceeds the unsigned 1..16 common profile")
        size = width * height
        image["components"].append({**component, "sample_kind": "unsigned",
                                    "samples": values[offset:offset + size]})
        offset += size
    return {"accepted": True, "image": image}


def _run_adapter(build, engine, format_name, encoded, work, iterations, expected, case, time_tool):
    samples = work / f"{engine}-{Path(build['path']).parents[1].name}-{iterations}.i64le"
    memory = samples.with_suffix(".rss")
    command = [build["path"], engine, format_name, str(encoded), str(samples), str(iterations)]
    process, elapsed, limited = framework._run_process_bounded(
        [time_tool, "-f", "%M", "-o", str(memory), *command], 90.0, 1 << 20, _limits,
    )
    record = {"engine": engine, "build": build["sha256"], "status": "process-error",
              "returncode": process.returncode, "process_elapsed_ms": elapsed,
              "observation": None, "reference_metrics": None, "peak_rss_bytes": None, "error": None}
    if limited:
        record["error"] = "comparison process exceeded its output bound"
        return record
    if process.returncode not in (0, 1):
        record["error"] = process.stderr.decode(errors="replace")[-4096:] or "comparison process failed"
        return record
    observation = json.loads(process.stdout)
    validate_observation(observation)
    if observation["engine"] != engine or observation["hayro_features"] != build["hayro_features"]:
        raise ValueError("comparison observation identifies the wrong engine or build features")
    record["observation"] = observation
    record["peak_rss_bytes"] = _peak_rss(memory)
    status = observation.get("status")
    if status != "decoded":
        if process.returncode != 1 or not observation.get("error"):
            raise ValueError("comparison error observation has inconsistent process status")
        record["status"] = "unsupported" if status == "rejected" and observation["unsupported"] else status
        record["error"] = observation["error"]
        return record
    if process.returncode != 0:
        raise ValueError("decoded observation came from an unsuccessful process")
    actual = read_observation(observation, samples, iterations)
    if expected is None:
        record["status"] = "accepted-without-reference"
        return record
    metrics = numerical.image_error_metrics(expected, actual)
    record["reference_metrics"] = metrics
    record["status"] = "qualified"
    if metrics["maximum_error"] > case.maximum_error or metrics["worst_component_rmse"] > case.maximum_rmse:
        record["status"] = "numerical-disagreement"
        record["error"] = "decoded output exceeds the declared independent-reference comparison budget"
    record["exact_reference_match"] = metrics["maximum_error"] == 0
    record["common_output_median_ms"] = statistics.median(t["common_output_ns"] for t in observation["timings"]) / 1_000_000
    record["decode_only_median_ms"] = statistics.median(t["decode_ns"] for t in observation["timings"]) / 1_000_000
    return record


def _prepare(case, high_throughput, work, tools):
    extension = "ppm" if case.channels == 3 else "pgm"
    source = work / f"source.{extension}"
    raw = work / ("encoded.j2c" if high_throughput or case.format != "jp2" else "encoded.jp2")
    source.write_bytes(numerical.source_image(case))
    options = (["-num_decomps", str(case.decomposition_levels), "-reversible", str(case.lossless).lower()]
               if high_throughput else ["-n", str(case.decomposition_levels + 1)])
    if case.codestream is None:
        numerical._run_checked([tools["encoder"], "-i", str(source), "-o", str(raw),
                                *options, *case.options], 30.0)
    else:
        raw.write_bytes(case.codestream)
    encoded = raw
    if case.format == "jph":
        encoded = work / "encoded.jph"
        encoded.write_bytes(framework.jp2_file(raw.read_bytes(), b"jph ", width=case.width,
                                               height=case.height, components=case.channels,
                                               precision=case.precision))
    reference = work / f"reference.{extension}"
    numerical._run_checked([tools["decoder"], "-i", str(encoded), "-o", str(reference)], 30.0)
    expected = framework.parse_pnm(reference)
    if case.lossless and framework.normalized_hash(expected) != framework.normalized_hash(framework.parse_pnm(source)):
        raise ValueError("independent comparison reference changed lossless source samples")
    return encoded, expected, {"input_sha256": framework.sha256_file(source),
                               "encoded_sha256": framework.sha256_file(encoded),
                               "reference_sha256": framework.normalized_hash(expected),
                               "encoder_invoked": case.codestream is None,
                               "encoder_options": [*options, *case.options] if case.codestream is None else []}


def write_summary(path, result):
    lines = [
        "# JPEG 2000 comparison with hayro-jpeg2000 0.4.1", "",
        f"- Execution status: **{result['status']}**; our independent baseline qualified: **{result['baseline_passed']}**.",
        f"- Source commit: `{result['provenance']['git_commit']}`; dirty checkout: `{result['provenance']['git_dirty']}`.",
        f"- Host: {result['environment']['system']}; CPU: {result['environment']['cpu_model']}.",
        f"- Compiler: `{result['environment']['rustc'].splitlines()[0]}`.",
        f"- Hayro crate checksum: `{result['reference']['checksum']}`.",
        f"- Samples: {result['repetitions']} processes x {result['iterations']} timed fresh-context decodes per qualified performance case.",
        "- One untimed warmup; input I/O, hashing and file writes are excluded from internal timers.",
        "- Main timing includes parse/decode, common planar integer conversion and native-state disposal.",
        "- Peak RSS is whole-process, including warmup/canonical output/observation work; it is not native decoder storage alone.",
        "- Generated unsigned 8/16-bit grayscale/RGB workloads are not a universal application-performance or conformance claim.",
    ]
    if result["blockers"]:
        lines += ["", "## Blockers", "", *[f"- {item}" for item in result["blockers"]]]
    if result["errors"]:
        lines += ["", "## Errors", "", *[f"- {item}" for item in result["errors"]]]
    if result["status"] == "blocked":
        path.write_text("\n".join(lines) + "\n")
        return
    lines += [
        "", "## Performance", "",
        "| Case | Ours ms | Hayro default ms | Hayro std-only ms | Ours/hayro time | Ours MiB | Hayro MiB | Exact common output |",
        "|---|---:|---:|---:|---:|---:|---:|---|",
    ]

    def value(record, key, divisor=1):
        return f"{record[key] / divisor:.2f}" if record and key in record else "N/A"

    for row in result["performance"]:
        ours = row["performance"].get("ours")
        default = row["performance"].get("hayro-default")
        scalar = row["performance"].get("hayro-scalar")
        exact = default["exact_output_match"] if default and "exact_output_match" in default else "not comparable"
        lines.append(
            f"| {row['id']} | {value(ours, 'common_output_median_ms')} | "
            f"{value(default, 'common_output_median_ms')} | {value(scalar, 'common_output_median_ms')} | "
            f"{value(default, 'ours_over_hayro_time_ratio')} | {value(ours, 'peak_rss_bytes', 2**20)} | "
            f"{value(default, 'peak_rss_bytes', 2**20)} | {exact} |"
        )
    summary = result["summary"]
    lines += [
        "", "A ratio greater than one means ours took longer. Unsupported cases are N/A, not fast decodes.",
        "Lossy outputs can qualify within declared reference-error budgets without matching each other exactly.",
        "The JSON report retains per-run measurements, exact-output flags, reference metrics and source/tool/input/output hashes.",
        "", "## Observed feature/output matrix", "",
        f"- Canonical operation cases: {summary['corpus_cases']}.",
        f"- Generated numerical cases: {summary['capability_cases']}; ours qualified {summary['ours_qualified']}.",
        f"- Hayro defaults qualified {summary['hayro_default_qualified']} and returned unsupported for {summary['hayro_default_unsupported']}.",
        f"- Hayro std-only qualified {summary['hayro_scalar_qualified']}.",
        "- The matrix intentionally includes many HT cases. These counts are not an unbiased feature-support percentage.",
        "- Metadata inspection and JPIP ingestion have no equivalent published hayro API and are explicitly not timed as image decodes.",
    ]
    for row in result["corpus"]:
        ours = row["engines"]["ours"]["status"]
        hayro = row["engines"]["hayro-default"]["status"]
        if hayro == "accepted-without-reference" and row["expected"] == "reject":
            lines.append(f"- Default acceptance-policy difference: `{row['id']}`; ours `{ours}`, hayro accepts. Hayro defaults are permissive; this is not a vulnerability or conformance finding.")
    matrix = Path(os.path.relpath(framework.VALIDATION / "COMPARISON.md", path.parent)).as_posix()
    lines += [
        "", f"See the [version-specific feature/API matrix and methodology](<{matrix}>) for documented/source-inspected versus tested support.",
        "", "## Limitations", "",
        "- This does not identify performance bottlenecks or explain the measured gap; profiling is a follow-up.",
        "- Reusable hayro Image/DecoderContext throughput, PDF-derived corpora, signed/nonuniform component profiles and complete high-precision behavior are not measured.",
        "- Neither decoder is certified against official Part 4 vectors by this comparison.",
        "- No production algorithm, dependency or verification pin was changed to improve benchmark results.", "",
    ]
    path.write_text("\n".join(lines))


def run_comparison(output_dir=None, iterations=5, repetitions=3, capabilities_only=False):
    if type(iterations) is not int or not 1 <= iterations <= 100 or type(repetitions) is not int or not 1 <= repetitions <= 10:
        raise ValueError("comparison iterations/repetitions must be bounded positive integers")
    destination = framework.report_path(output_dir, "hayro-comparison.json")
    result = {
        "$schema": framework.report_schema(output_dir, "hayro-comparison.schema.json"),
        "schema_version": 1, "status": "blocked", "baseline_passed": False,
        "scope": "Generated unsigned 8/16-bit components; fresh parse/decode/context and common rounded-integer planar output. Not a conformance certificate or universal speed claim.",
        "provenance": framework.source_binding(), "blockers": [], "errors": [],
        "reference": {"crate": "hayro-jpeg2000", "version": HAYRO_VERSION,
                      "checksum": HAYRO_CHECKSUM, "vcs_revision": HAYRO_REVISION},
        "environment": {"system": platform.platform(), "machine": platform.machine(),
                        "cpu_count": os.cpu_count(),
                        "cpu_model": next((line.split(":", 1)[1].strip()
                                           for line in Path("/proc/cpuinfo").read_text().splitlines()
                                           if line.startswith("model name")), None)
                        if platform.system() == "Linux" else None,
                        "hayro_settings": {"strict": False, "resolve_palette_indices": True,
                                           "target_resolution": None},
                        "rustc": subprocess.check_output(["rustc", "-vV"], cwd=framework.ROOT, text=True).strip(),
                        "rustflags": os.environ.get("RUSTFLAGS", "")},
        "comparison_source_hashes": {str(path.relative_to(framework.ROOT)): framework.sha256_file(path)
                                     for path in [MANIFEST, MANIFEST.with_name("Cargo.lock"),
                                                  MANIFEST.parent / "src/main.rs"]},
        "iterations": iterations, "repetitions": repetitions, "capabilities_only": capabilities_only,
        "builds": {}, "tools": {}, "corpus": [], "capabilities": [], "performance": [],
    }
    tools = {}
    for role, variable, default in (
        ("legacy_encoder", "OPENJPEG_ENCODER", "opj_compress"),
        ("legacy_decoder", "OPENJPEG_DECODER", "opj_decompress"),
        ("ht_encoder", "OPENJPH_ENCODER", "ojph_compress"),
        ("ht_decoder", "OPENJPH_DECODER", "ojph_expand"), ("time", "JPEG2000_TIME", "time"),
    ):
        configured = os.environ.get(variable)
        path = shutil.which(configured or default)
        if path is None:
            if configured:
                raise FileNotFoundError(f"configured comparison tool is unavailable: {variable}")
            result["blockers"].append(f"comparison tool unavailable: {default}")
        else:
            tools[role] = path
            result["tools"][role] = {"path": path, "sha256": framework.sha256_file(Path(path))}
    if framework.resource is None or platform.system() != "Linux":
        result["blockers"].append("comparison process RSS/enforcement requires Linux/GNU Time")
    if result["blockers"]:
        framework.validate_schema(SCHEMA, result)
        framework.write_json(destination, result)
        write_summary(destination.with_suffix(".md"), result)
        return result
    version = subprocess.run([tools["time"], "--version"], capture_output=True, check=True)
    if b"GNU" not in version.stdout:
        raise ValueError("comparison process RSS measurements require GNU Time")
    result["builds"] = build_adapters()
    result["status"] = "running"
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="hayro-comparison-", dir=destination.parent) as directory:
        root = Path(directory)
        ordinary_subject = framework.build_subject(release=True)
        minimal = {"accepted": True, "image": {"width": 1, "height": 1, "components": [{
            "width": 1, "height": 1, "precision": 8, "signed": False,
            "sample_kind": "unsigned", "samples": [128],
        }]}}
        for generated in framework.generated_cases():
            work = root / generated.case_id
            work.mkdir()
            encoded = work / f"input.{generated.format}"
            encoded.write_bytes(generated.data)
            row = {"id": generated.case_id, "operation": generated.operation, "format": generated.format,
                   "expected": generated.expected, "input_sha256": framework.sha256_file(encoded),
                   "engines": {}}
            if generated.operation != "decode":
                process, _, limited = framework._run_process_bounded(
                    [str(ordinary_subject), generated.operation, generated.format, str(encoded)], 10.0, 1 << 20, _limits,
                )
                observed = framework.parse_subject_output(process.stdout, process.stderr, process.returncode)
                wanted = generated.expected == "accept"
                passed = not limited and not observed.get("execution_failed") and observed["accepted"] == wanted
                row["engines"]["ours"] = {"status": "expected-outcome" if passed else "unexpected-outcome",
                                          "observation": observed}
                for label in ("hayro-default", "hayro-scalar"):
                    row["engines"][label] = {"status": "no-equivalent-api",
                                             "reason": "published hayro Image API does not expose this container-inspection/JPIP-ingestion operation"}
                if not passed:
                    result["errors"].append(f"{generated.case_id}: our metadata operation did not match its declared outcome")
            else:
                expected = minimal if generated.expected == "accept" else None
                case = numerical.NumericalCase(generated.case_id, width=1, height=1)
                for label, build, engine in (
                    ("ours", result["builds"]["default"], "ours"),
                    ("hayro-default", result["builds"]["default"], "hayro"),
                    ("hayro-scalar", result["builds"]["scalar"], "hayro"),
                ):
                    record = _run_adapter(build, engine, generated.format, encoded, work, 1,
                                          expected, case, tools["time"])
                    row["engines"][label] = record
                    passed = record["status"] == "qualified" if expected is not None else record["status"] in ("rejected", "unsupported")
                    if label == "ours" and not passed:
                        result["errors"].append(f"{generated.case_id}: our baseline did not match its declared outcome")
            result["corpus"].append(row)
        matrix = [(case, False, False) for case in numerical.CASES]
        matrix += [(case, True, False) for case in numerical.HT_CASES]
        if not capabilities_only:
            matrix += [(case, high_throughput, True) for case, high_throughput in PERFORMANCE_CASES]
        for case, high_throughput, performance in matrix:
            work = root / case.name
            work.mkdir()
            reference_tools = {"encoder": tools["ht_encoder" if high_throughput else "legacy_encoder"],
                               "decoder": tools["ht_decoder" if high_throughput else "legacy_decoder"]}
            row = {"id": case.name, "format": case.format, "precision": case.precision,
                   "channels": case.channels, "width": case.width, "height": case.height,
                   "lossless": case.lossless, "high_throughput": high_throughput,
                   "thresholds": {"maximum_error": case.maximum_error, "maximum_rmse": case.maximum_rmse},
                   "bindings": None, "engines": {}, "performance": {}, "error": None, "artifacts": []}
            try:
                encoded, expected, row["bindings"] = _prepare(case, high_throughput, work, reference_tools)
                for label, build, engine in (
                    ("ours", result["builds"]["default"], "ours"),
                    ("hayro-default", result["builds"]["default"], "hayro"),
                    ("hayro-scalar", result["builds"]["scalar"], "hayro"),
                ):
                    preflight = _run_adapter(build, engine, case.format, encoded, work, 1,
                                             expected, case, tools["time"])
                    row["engines"][label] = preflight
                    if label == "ours" and preflight["status"] != "qualified":
                        result["errors"].append(f"{case.name}: our baseline {preflight['status']}")
                    if performance and preflight["status"] == "qualified":
                        runs = []
                        row["performance"][label] = {"runs": runs}
                        for repeat in range(repetitions):
                            run_work = work / f"{label}-{repeat}"
                            run_work.mkdir()
                            measured = _run_adapter(build, engine, case.format, encoded, run_work,
                                                    iterations, expected, case, tools["time"])
                            runs.append(measured)
                            if (measured["status"] != "qualified"
                                    or measured["observation"]["output_sha256"] != preflight["observation"]["output_sha256"]):
                                raise ValueError(f"{label} changed outcome/output after preflight: {measured['status']}")
                        row["performance"][label] = {
                            "runs": runs,
                            "common_output_median_ms": statistics.median(
                                timing["common_output_ns"] for run in runs
                                for timing in run["observation"]["timings"]) / 1_000_000,
                            "peak_rss_bytes": max(run["peak_rss_bytes"] for run in runs),
                        }
                ours = row["performance"].get("ours")
                for label in ("hayro-default", "hayro-scalar"):
                    competitor = row["performance"].get(label)
                    if ours and competitor:
                        competitor["ours_over_hayro_time_ratio"] = ours["common_output_median_ms"] / competitor["common_output_median_ms"]
                        competitor["exact_output_match"] = (row["engines"]["ours"]["observation"]["output_sha256"]
                                                             == row["engines"][label]["observation"]["output_sha256"])
            except (OSError, ValueError, subprocess.SubprocessError) as error:
                row["error"] = str(error)
                result["errors"].append(f"{case.name}: {error}")
            if row["error"] or any(item["status"] not in ("qualified", "unsupported")
                                   for item in row["engines"].values()):
                saved = framework.report_path(output_dir, f"comparison-failures/{case.name}")
                shutil.copytree(work, saved, dirs_exist_ok=True)
                row["artifacts"].append(saved.relative_to(destination.parent).as_posix())
            result["performance" if performance else "capabilities"].append(row)
            framework.write_json(destination, result)
    result["baseline_passed"] = not result["errors"]
    result["status"] = "failed" if result["errors"] else "completed"
    result["summary"] = {
        "corpus_cases": len(result["corpus"]),
        "capability_cases": len(result["capabilities"]), "performance_cases": len(result["performance"]),
        "ours_qualified": sum(row["engines"].get("ours", {}).get("status") == "qualified"
                              for row in result["capabilities"]),
        "hayro_default_qualified": sum(row["engines"].get("hayro-default", {}).get("status") == "qualified"
                                       for row in result["capabilities"]),
        "hayro_default_unsupported": sum(row["engines"].get("hayro-default", {}).get("status") == "unsupported"
                                         for row in result["capabilities"]),
        "hayro_scalar_qualified": sum(row["engines"].get("hayro-scalar", {}).get("status") == "qualified"
                                      for row in result["capabilities"]),
    }
    framework.validate_schema(SCHEMA, result)
    framework.write_json(destination, result)
    write_summary(destination.with_suffix(".md"), result)
    return result
