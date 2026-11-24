#!/usr/bin/env python3
"""RUSTC_WRAPPER and native-linker wrapper; preserve every invocation."""

import json
import os
from pathlib import Path
import sys
import uuid

from measure import measure

if Path(sys.argv[0]).name.startswith("linker"):
    mode, command = "link", [os.environ["CONSUMER_REAL_LINKER"], *sys.argv[1:]]
elif sys.argv[1:2] == ["--cc"]:
    mode, command = "cc", sys.argv[2:]
else:
    mode, command = "rustc", sys.argv[1:]
prefix = Path(os.environ["CONSUMER_INVOCATIONS"]) / (mode + "-" + uuid.uuid4().hex)
metrics = measure(command, prefix, preserve_jobserver=mode == "rustc")
Path(str(prefix) + ".environment.json").write_text(json.dumps({
    key: value for key, value in os.environ.items()
    if key in {"RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_JOBS"}
    or key.startswith("CARGO_PROFILE_RELEASE_")
}, indent=2) + "\n")
sys.stdout.write(Path(str(prefix) + ".stdout").read_text())
sys.stderr.write(Path(str(prefix) + ".stderr").read_text())
sys.exit(metrics["returncode"])
