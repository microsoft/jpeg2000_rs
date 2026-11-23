#!/usr/bin/env python3
"""Untimed API/output qualification before spending remote benchmark minutes."""

import json
import os
from pathlib import Path
import subprocess

from run import BACKENDS, HERE, ROOT, check_outcome, configuration_environment

output = ROOT / "target/consumer-tuning/smoke"
output.mkdir(parents=True, exist_ok=True)
fixtures_path = ROOT / "target/consumer-tuning/fixtures/manifest.json"
fixtures = json.loads(fixtures_path.read_text())["fixtures"]
outcomes = {}
for backend in BACKENDS:
    directory = output / backend
    directory.mkdir(exist_ok=True)
    invocations = directory / "invocations"
    invocations.mkdir(exist_ok=True)
    env = configuration_environment("generic", directory / "target", invocations)
    subprocess.run(["cargo", "+1.93.1", "build", "--release", "--locked", "--manifest-path",
                    str(HERE / "Cargo.toml"), "--no-default-features", "--features", backend],
                   env=env, check=True)
    executable = directory / "target/release/jpeg2000-final-consumer-bench"
    outcomes[backend] = {}
    for fixture in fixtures:
        result = subprocess.run([executable, fixtures_path.parent / fixture["path"], "1"],
                                capture_output=True, text=True, check=True)
        outcome = json.loads(result.stdout)["outcome"]
        check_outcome(backend, fixture, outcome)
        outcomes[backend][fixture["id"]] = outcome
    print(f"{backend}: {len(fixtures)} API/shape/source/output checks passed (timing discarded)", flush=True)
assert outcomes["current"] == outcomes["release022"], "main/release control mismatch"
(output / "outcomes.json").write_text(json.dumps(outcomes, indent=2) + "\n")
