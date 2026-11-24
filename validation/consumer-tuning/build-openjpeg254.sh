#!/usr/bin/env bash
set -euo pipefail

root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
output="$root/target/consumer-tuning/encoder"
source_dir="$output/source"
build_dir="$output/build"
revision=6c4a29b00211eb0430fa0e5e890f1ce5c80f409f

if [ "${1:-}" = --source-only ]; then
    [ "$#" = 2 ]
    source_dir="$2"
    output=$(dirname -- "$source_dir")
fi
mkdir -p "$output"
if [ ! -e "$source_dir" ]; then
    if [ "${1:-}" = --source-only ]; then
        git clone --depth 1 --branch v2.5.4 --no-checkout https://github.com/uclouvain/openjpeg.git "$source_dir"
    else
        git clone --no-checkout https://github.com/uclouvain/openjpeg.git "$source_dir"
    fi
    git -C "$source_dir" checkout --detach "$revision"
fi
if [ ! -d "$source_dir/.git" ] ||
    [ "$(git -C "$source_dir" rev-parse HEAD)" != "$revision" ] ||
    [ -n "$(git -C "$source_dir" status --porcelain)" ]; then
    echo "Expected clean OpenJPEG 2.5.4 source at $revision" >&2
    exit 1
fi
if [ "${1:-}" = --source-only ]; then
    printf 'OpenJPEG 2.5.4 source revision: %s\n' "$revision"
    exit 0
fi
cmake -S "$source_dir" -B "$build_dir" \
    -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=OFF \
    -DCMAKE_POLICY_VERSION_MINIMUM=3.5 \
    -DBUILD_CODEC=ON -DBUILD_TESTING=OFF -DBUILD_JPIP=OFF \
    -DCMAKE_DISABLE_FIND_PACKAGE_PNG=TRUE -DCMAKE_DISABLE_FIND_PACKAGE_TIFF=TRUE \
    -DCMAKE_DISABLE_FIND_PACKAGE_LCMS2=TRUE -DCMAKE_DISABLE_FIND_PACKAGE_LCMS=TRUE
cmake --build "$build_dir" --parallel 2 --target opj_compress
printf 'OpenJPEG 2.5.4 source revision: %s\n' "$revision"
