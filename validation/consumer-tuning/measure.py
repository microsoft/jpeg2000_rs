#!/usr/bin/env python3
"""Linux process measurement; RSS values are explicitly not allocation counts."""

import json
import os
from pathlib import Path
import re
import subprocess
import time


def tree_rss_kib(pid):
    """Sample summed resident sets; shared pages can be counted more than once."""
    try:
        status = Path(f"/proc/{pid}/status").read_text()
        rss = next((int(line.split()[1]) for line in status.splitlines()
                    if line.startswith("VmRSS:")), 0)
        children = set()
        for task in Path(f"/proc/{pid}/task").iterdir():
            try:
                children.update((task / "children").read_text().split())
            except (FileNotFoundError, ProcessLookupError, PermissionError):
                continue
        return rss + sum(tree_rss_kib(int(child)) for child in children)
    except (FileNotFoundError, ProcessLookupError, PermissionError):
        return 0


def measure(command, prefix, env=None, sample_tree=False, preserve_jobserver=False,
            *, extended=False, cwd=None, timeout_s=None):
    prefix = Path(prefix)
    prefix.parent.mkdir(parents=True, exist_ok=True)
    if prefix.with_suffix(".time.json").exists():
        raise FileExistsError(prefix)
    time_file = str(prefix) + ".time.json"
    fields = '{"user_s":%U,"system_s":%S,"max_process_rss_kib":%M,"exit":%x'
    if extended:
        fields += (',"minor_faults":%R,"major_faults":%F,'
                   '"voluntary_context_switches":%w,"involuntary_context_switches":%c')
    wrapped = ["/usr/bin/time", "-q", "-f", fields + "}",
               "-o", time_file, *map(str, command)]
    if timeout_s is not None:
        # Time the target, not the watchdog. A killed watchdog may leave no GNU time output.
        wrapped = ["/usr/bin/timeout", "--kill-after=5s", f"{timeout_s}s", *wrapped]
    start = time.perf_counter_ns()
    peak = 0
    pass_fds = ()
    if preserve_jobserver:
        flags = (env or os.environ).get("CARGO_MAKEFLAGS", "")
        jobserver = re.search(r"--jobserver-(?:auth|fds)=(\d+),(\d+)", flags)
        if jobserver:
            pass_fds = tuple(map(int, jobserver.groups()))
            for fd in pass_fds:
                os.fstat(fd)
    with open(str(prefix) + ".stdout", "w") as stdout, \
            open(str(prefix) + ".stderr", "w") as stderr:
        process = subprocess.Popen(wrapped, env=env, stdout=stdout, stderr=stderr,
                                   pass_fds=pass_fds, cwd=cwd)
        if sample_tree:
            while process.poll() is None:
                peak = max(peak, tree_rss_kib(process.pid))
                time.sleep(0.05)
        code = process.wait()
    elapsed = time.perf_counter_ns() - start
    try:
        metrics = json.loads(Path(time_file).read_text())
    except (OSError, ValueError):
        if timeout_s is None or code == 0:
            raise
        metrics = {"exit": None, "measurement_unavailable": "GNU time did not report"}
    metrics.update({"wall_ns": elapsed, "command": list(map(str, command)),
                    "returncode": code, "sampled_tree_rss_kib": peak if sample_tree else None,
                    "pid": process.pid})
    if timeout_s is not None:
        metrics["launch_argv"] = wrapped
    Path(str(prefix) + ".metrics.json").write_text(json.dumps(metrics, indent=2) + "\n")
    return metrics
