"""Audit actual original-consumer flags and matched shim/FFI decoder archives."""

import argparse
import hashlib
import json
from pathlib import Path
import shlex
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--crate", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--prefix", default="")
    args = parser.parse_args()
    result = {}
    for backend, name in (("openjpeg", "Openjpeg"), ("shim", "Shim"), ("ffi", "Ffi")):
        out = args.work.resolve() / "out" / (name if backend == "openjpeg" else args.prefix + name)
        commands = subprocess.check_output([str(args.work / "third_party/ninja/ninja"), "-C", str(out),
                                            "-t", "commands", "jp2_eval"]).decode("latin1")
        count = 0
        for line in commands.splitlines():
            tokens = shlex.split(line)
            if "-c" not in tokens or not any("/clang" in i for i in tokens[:2]):
                continue
            opts = [i for i in tokens if i in ("-O0", "-O1", "-O2", "-O3", "-Os", "-Oz", "-Ofast")]
            assert opts[-1] == "-O3" and "-mcpu=native" in tokens and "-flto=thin" in tokens
            assert "-DNDEBUG" in tokens and "-D_DEBUG" not in tokens and "-ffast-math" not in tokens
            count += 1
        link = next(line for line in commands.splitlines() if "--lto-O" in line and "jp2_eval" in line)
        assert "-Wl,--lto-O3" in shlex.split(link)
        page = next(line for line in commands.splitlines() if "cpdf_dib.cpp -o" in line)
        assert "-DPDF_EVAL_JPX_LENIENT" in shlex.split(page), "A CLI strict=false argument alone does not set page-render policy."
        row = dict(c_cpp_o3_native_thinlto_commands=count, final_lto_opt=3,
                   pdf_jpx_lenient=True,
                   binary_sha256=hashlib.sha256((out / "jp2_eval").read_bytes()).hexdigest())
        if backend != "openjpeg":
            flags_files = ["obj/third_party/jpeg2000_decoder/lib.rsp.rust"]
            flags_files += ["obj/third_party/jpeg2000_decoder/compat.rsp.rust"] if backend == "shim" else ["obj/core/fxcodec/rust_jpx_ffi.rsp.rust"]
            for name in flags_files:
                flags = (out / name).read_text().splitlines()
                for wanted in ("-Copt-level=3", "-Ctarget-cpu=native", "-Ccodegen-units=1",
                               "-Cdebug-assertions=no", "-Coverflow-checks=no", "-Clinker-plugin-lto=yes"):
                    assert wanted in flags, (backend, name, wanted)
            row["core_archive_sha256"] = hashlib.sha256(
                (out / "obj/third_party/jpeg2000_decoder/libjpeg2000_decoder.rlib").read_bytes()).hexdigest()
            if backend == "shim":
                c_line = next(line for line in commands.splitlines() if "/shim.c -o" in line)
                tokens = shlex.split(c_line)
                source = (out / tokens[tokens.index("-c") + 1]).resolve()
                assert source == (args.crate / "adapters/openjpeg-capi/shim.c").resolve(), "Mixed C/Rust shim source revisions."
                row["same_revision_c_shim_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
        result[backend] = row
    assert result["shim"]["core_archive_sha256"] == result["ffi"]["core_archive_sha256"]
    result["crate_source"] = subprocess.check_output(["git", "-C", str(args.crate), "rev-parse", "HEAD"], text=True).strip()
    assert subprocess.check_output(["git", "-C", str(args.crate), "status", "--porcelain"], text=True) == ""
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
