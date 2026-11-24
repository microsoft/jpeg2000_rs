"""Apply the original consumer overlay to a disposable public PDFium base."""

import argparse
from pathlib import Path
import shutil
import subprocess

BUNDLE = Path(__file__).resolve().parent
BASE = "68f43efa71ac66ba843ba286bb76d075aa1c49df"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdfium", required=True, type=Path)
    parser.add_argument("--crate", required=True, type=Path)
    parser.add_argument("--clang", required=True, type=Path)
    parser.add_argument("--rust", required=True, type=Path)
    parser.add_argument("--prepared", action="store_true", help="Exact disposable copy of the original evaluator only")
    args = parser.parse_args()
    root, crate, clang, rust = (p.resolve() for p in (args.pdfium, args.crate, args.clang, args.rust))
    if not args.prepared:
        sha = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(root), "status", "--porcelain", "--untracked-files=no"], text=True)
        if sha != BASE or dirty:
            raise SystemExit("Use a clean disposable public base with its Rust/CXX DEPS, not a working checkout.")
        subprocess.run(["git", "-C", str(root), "apply", "--check", str(BUNDLE / "consumer/integration.patch")], check=True)
        subprocess.run(["git", "-C", str(root), "apply", str(BUNDLE / "consumer/integration.patch")], check=True)
        subprocess.run(["git", "-C", str(root), "apply", str(BUNDLE / "consumer/compiler.patch")], check=True)
    elif (root / "jp2_eval.cpp").read_bytes() != (BUNDLE / "consumer/jp2_eval.cpp").read_bytes():
        raise SystemExit("--prepared requires the exact original disposable consumer source.")
    rust_version = subprocess.check_output([str(rust / "bin/rustc"), "--version"], text=True).strip()
    common = f'''
target_cpu = "arm64"
use_remoteexec = false
is_debug = false
is_component_build = false
pdf_is_standalone = true
pdf_use_skia = false
pdf_enable_fontations = false
pdf_enable_xfa = false
pdf_enable_v8 = false
pdf_enable_rust_png = false
clang_base_path = "{clang}"
clang_use_chrome_plugins = false
use_mold = false
use_lld = true
use_thin_lto = true
optimize_for_size = false
symbol_level = 0
dcheck_always_on = false
enable_rust = true
enable_rust_cxx = true
rust_sysroot_absolute = "{rust}"
rust_bindgen_root = "{rust}"
rustc_version = "{rust_version}"
added_rust_stdlib_libs = [ "addr2line", "adler2", "gimli", "miniz_oxide", "panic_unwind" ]
pdf_eval_jpx_lenient = true
'''
    for name, compat, ffi in (("Openjpeg", False, False), ("Shim", True, False), ("Ffi", False, True)):
        text = common + f"\npdf_use_openjpeg_compat = {str(compat).lower()}\npdf_enable_rust_jpeg2000 = {str(ffi).lower()}\n"
        if compat or ffi:
            text += f'pdf_eval_jpeg2000_core_root = "{crate}"\n'
        if compat:
            text += f'pdf_eval_jpeg2000_compat_root = "{crate}/adapters/openjpeg-capi"\n'
        if ffi:
            text += "pdf_enable_rust_jpeg2000_pdf_recovery = false\n"
        subprocess.run([str(root / "buildtools/linux64/gn"), "gen", str(root / "out" / name),
                        "--args=" + text], cwd=root, check=True)
    print("Configured Openjpeg/Shim/Ffi; audit actual commands and equal crate archives before timing.")


if __name__ == "__main__":
    main()
