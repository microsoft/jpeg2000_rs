#!/usr/bin/env python3
"""Recompute paired summaries without discarding raw process observations."""

import collections
import json
import math
from pathlib import Path
import random
import statistics
import sys


def geometric(values):
    return math.exp(statistics.mean(math.log(value) for value in values))


def interval(values):
    rng = random.Random(449)
    draws = sorted(geometric(rng.choices(values, k=len(values))) for _ in range(4000))
    return [draws[99], draws[3899]]


def summarize(output):
    rows = [json.loads(line) for line in (output / "samples.jsonl").read_text().splitlines()]
    fixtures = {f["id"]: f for f in json.loads((output / "fixture-manifest.json").read_text())["fixtures"]}
    grouped = collections.defaultdict(dict)
    process_groups = collections.defaultdict(list)
    for row in rows:
        key = row["backend"], row["tuned"], row["fixture"], row["pair"]
        grouped[key][row["config"]] = statistics.median(row["decode_ns"])
        process_groups[row["backend"], row["config"], row["fixture"]].append(row)
    ratios = collections.defaultdict(list)
    cohort_pairs = collections.defaultdict(list)
    for (backend, config, fixture, pair), values in grouped.items():
        ratio = values[config] / values["generic"]
        ratios[backend, config, fixture].append((pair, ratio))
        if fixtures[fixture]["group"] == "generated-1024":
            cohort_pairs[backend, config, pair].append(ratio)
    fixture_summary = []
    for (backend, config, fixture), values in ratios.items():
        ordered = [value for _, value in sorted(values)]
        fixture_summary.append({
            "backend": backend, "config": config, "fixture": fixture,
            "pairs": len(values), "tuned_over_generic_geomean": geometric(ordered),
            "paired_bootstrap_95_ratio": interval(ordered),
            "generic_first_ratios": [value for pair, value in values if pair % 2 == 0],
            "tuned_first_ratios": [value for pair, value in values if pair % 2 == 1],
        })
    cohort = collections.defaultdict(list)
    for (backend, config, pair), values in cohort_pairs.items():
        cohort[backend, config].append((pair, geometric(values)))
    cohort_summary = [{
        "backend": backend, "config": config, "pairs": len(values),
        "generated_16_inputs_ratio": geometric([value for _, value in values]),
        "decode_reduction_percent": 100 * (1 - geometric([value for _, value in values])),
        "paired_bootstrap_95_ratio": interval([value for _, value in values]),
        "pair_ratios": dict(values),
    } for (backend, config), values in cohort.items()]
    processes = []
    for (backend, config, fixture), values in process_groups.items():
        times = [statistics.median(value["decode_ns"]) for value in values]
        processes.append({
            "backend": backend, "config": config, "fixture": fixture, "processes": len(values),
            "decode_ns_median": statistics.median(times), "decode_ns_min": min(times),
            "decode_ns_max": max(times),
            "process_rss_kib_max": max(value["metrics"]["max_process_rss_kib"] for value in values),
            "process_rss_kib_median": statistics.median(
                value["metrics"]["max_process_rss_kib"] for value in values),
        })
    comparator = []
    indexed = {(row["backend"], row["config"], row["fixture"]): row for row in processes}
    for config in ["generic", "cpu", "thinlto", "cgu1", "combined"]:
        values = []
        for fixture in fixtures.values():
            if fixture["group"] != "generated-1024":
                continue
            current = indexed["current", config, fixture["id"]]["decode_ns_median"]
            hayro = indexed["hayro-scalar", config, fixture["id"]]["decode_ns_median"]
            values.append(current / hayro)
        comparator.append({"config": config, "current_over_hayro_scalar_geomean": geometric(values),
                           "per_fixture_ratios": values, "pixel_oracle": False,
                           "timing_pairing": "not decoder-paired; config comparisons are paired"})
    builds = [json.loads(line) for line in (output / "builds.jsonl").read_text().splitlines()]
    build_summary = []
    for row in builds:
        directory = output / f"build-{row['round']}-{row['config']}-{row['backend']}"
        binary = json.loads((directory / "binary.json").read_text())
        links = [json.loads(path.read_text())
                 for path in (directory / "invocations").glob("link-*.metrics.json")]
        build_summary.append({
            "round": row["round"], "backend": row["backend"], "config": row["config"],
            "build_wall_s": row["metrics"]["wall_ns"] / 1e9,
            "build_max_process_rss_kib": row["metrics"]["max_process_rss_kib"],
            "build_sampled_summed_tree_rss_kib": row["metrics"]["sampled_tree_rss_kib"],
            "binary_bytes": binary["bytes"], "binary_sha256": binary["sha256"],
            "native_link_invocations": len(links),
            "native_link_wall_s_sum": sum(link["wall_ns"] for link in links) / 1e9,
            "native_link_rss_kib_max": max((link["max_process_rss_kib"] for link in links), default=0),
        })
    result = {
        "schema": 1, "cohort": cohort_summary, "fixtures": fixture_summary,
        "processes": processes, "builds": build_summary, "comparator": comparator,
        "uncertainty": "4000 deterministic bootstrap resamples of matched pair blocks; "
                       "95% percentile interval for geometric tuned/generic ratio. "
                       "Only 4 pairs by default: exploratory, not a population/hardware guarantee. "
                       "Both JP2/J2K encodings of each source are correlated, not 16 independent images.",
        "memory": "KiB. GNU time max_process_rss is maximum single-process RSS in the tree. "
                  "Decode RSS includes startup, input and post-timing sample hashing. "
                  "Build summed-tree RSS sampled every 20ms can miss peaks and double-count shared pages.",
        "link_time": "Native cc linker invocation wall time, including wrapper overhead. "
                     "LLVM ThinLTO optimization runs inside rustc before native link; "
                     "rustc invocation wall time is retained separately; neither is pure LLVM link-only time.",
    }
    (output / "summary.json").write_text(json.dumps(result, indent=2) + "\n")
    for row in cohort_summary:
        print(f"{row['backend']:12} {row['config']:8} reduction={row['decode_reduction_percent']:+.2f}% "
              f"ratio95={row['paired_bootstrap_95_ratio']}")
    return result


if __name__ == "__main__":
    summarize(Path(sys.argv[1]).resolve())
