#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 6 ]; then
    echo "usage: bash expanded.sh OUTPUT OPENJPEG_SOURCE ENCODER DECODER_SOURCE CPU ASSET_CACHE" >&2
    exit 2
fi

here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mkdir -- "$1"
output=$(cd -- "$1" && pwd)
python3 "$here/corpus.py" --output "$output/corpus" --assets "$6" --encoder "$3"

# Build each requested configuration; this short run is not performance evidence.
python3 "$here/run.py" --output "$output/build-check" --openjpeg-source "$2" \
    --decoder-source "$4" --corpus-manifest "$output/corpus/manifest.json" \
    --configs generic,consumer,native --case '^style-b32-m0$' --cpu "$5" \
    --iterations 2 --minimum-ms 0 --warmups 0

rust="$output/build-check/generic/cargo/release/bench-vs-openjpeg"
openjpeg="$output/build-check/generic/bench-openjpeg"
python3 "$here/qualify.py" --manifest "$output/corpus/manifest.json" \
    --rust "$rust" --openjpeg "$openjpeg" --output "$output/qualification-full" \
    --qualified-manifest "$output/corpus/qualified-full.json" --cpu "$5"
python3 "$here/run.py" --output "$output/timings" --openjpeg-source "$2" \
    --reuse-builds "$output/build-check" --corpus-manifest "$output/corpus/qualified-full.json" \
    --configs generic,consumer,native --case '^(?!roi8k)' --cpu "$5"

bash "$here/partial.sh" "$output/build-check" "$output/corpus/manifest.json" \
    "$output/partial" "$2" "$5"
