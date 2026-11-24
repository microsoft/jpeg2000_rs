import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess

ROOT = Path(os.environ["JPX_EVAL_RESULTS"]).resolve()
BINARIES = {k: Path(v) for k, v in json.loads(os.environ["JPX_EVAL_BINARIES"]).items()}
FIELDS = ["status", "width", "height", "channels", "color", "p50_us", "p90_us", "runs"]

def save_json(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n")

def limits():
    resource.setrlimit(resource.RLIMIT_DATA, (2 * 1024**3, 2 * 1024**3))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

def run(backend, item, mode, reduce=0, indexed=False, runs=0, label="functional",
        binary=None):
    out = ROOT / "pixels" / label / backend
    out.mkdir(parents=True, exist_ok=True)
    name = hashlib.sha256(f"{item['id']}:{mode}:{reduce}:{indexed}".encode()).hexdigest()[:20]
    target = out / f"{name}.bin"
    command = [str(binary if binary is not None else BINARIES[backend]), "pdf" if item["group"] == "pdf" else "image",
               item["path"], str(target), str(int(mode == "strict")),
               str(reduce), str(int(indexed)), str(runs)]
    environment = os.environ.copy()
    environment.pop("OPJ_NUM_THREADS", None)
    try:
        completed = subprocess.run(command, capture_output=True, text=True,
                                   timeout=120 if runs else 15, preexec_fn=limits,
                                   env=environment)
    except subprocess.TimeoutExpired as error:
        return dict(status="timeout", stderr=str(error), path="")
    if completed.returncode:
        return dict(status=f"exit_{completed.returncode}", stderr=completed.stderr,
                    stdout=completed.stdout, path="")
    values = completed.stdout.strip().split("\t")
    if len(values) != len(FIELDS):
        raise RuntimeError(f"Unexpected harness output: {completed.stdout!r}")
    result = dict(zip(FIELDS, values))
    result["stderr"] = completed.stderr
    result["path"] = str(target) if target.exists() else ""
    if result["status"] == "ok":
        data = target.read_bytes()
        result["sha256"] = hashlib.sha256(data).hexdigest()
        result["bytes"] = len(data)
    return result

def compare(a, b):
    if a["status"] != "ok" or b["status"] != "ok":
        return dict(comparison="not_both_accepted")
    if any(a[field] != b[field] for field in ("width", "height", "channels")):
        return dict(comparison="layout_differs")
    if a["sha256"] == b["sha256"]:
        return dict(comparison="exact", max_delta=0, different_samples=0, mae=0, mse=0)
    x, y = Path(a["path"]).read_bytes(), Path(b["path"]).read_bytes()
    if len(x) != len(y):
        return dict(comparison="layout_differs")
    deltas = [abs(p - q) for p, q in zip(x, y)]
    return dict(comparison="pixels_differ", max_delta=max(deltas),
                different_samples=sum(d != 0 for d in deltas),
                samples=len(deltas), mae=sum(deltas) / len(deltas),
                mse=sum(d*d for d in deltas) / len(deltas))
