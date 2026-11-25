#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 5 ]; then
    echo "usage: bash partial.sh COMPLETE_BUILDS MANIFEST FRESH_OUTPUT OPENJPEG_SOURCE CPU" >&2
    exit 2
fi

here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
baseline=$(cd -- "$1" && pwd)
test -f "$baseline/COMPLETE.json"
manifest_dir=$(cd -- "$(dirname -- "$2")" && pwd)
manifest="$manifest_dir/$(basename -- "$2")"
mkdir -- "$3"
output=$(cd -- "$3" && pwd)
qualified="$manifest_dir/qualified-$(basename -- "$output")"
rust="$baseline/generic/cargo/release/bench-vs-openjpeg"
openjpeg="$baseline/generic/bench-openjpeg"

for reduce in 1 2 3; do
    python3 "$here/qualify.py" --manifest "$manifest" \
        --rust "$rust" --openjpeg "$openjpeg" --output "$output/qualification-reduce-$reduce" \
        --qualified-manifest "$qualified-reduce-$reduce.json" \
        --case '^roi8k' --reduce "$reduce" --cpu "$5"
    python3 "$here/run.py" --output "$output/reduce-$reduce" --openjpeg-source "$4" \
        --reuse-builds "$baseline" --corpus-manifest "$qualified-reduce-$reduce.json" \
        --configs generic,consumer,native --reduce "$reduce" --cpu "$5"
done
python3 "$here/qualify.py" --manifest "$manifest" \
    --rust "$rust" --openjpeg "$openjpeg" --output "$output/qualification-window" \
    --qualified-manifest "$qualified-window.json" --case '^roi8k' \
    --window 2048,2048,512,512 --check-window-crop --cpu "$5"
python3 "$here/run.py" --output "$output/window" --openjpeg-source "$4" \
    --reuse-builds "$baseline" --corpus-manifest "$qualified-window.json" \
    --configs generic,consumer,native --window 2048,2048,512,512 --cpu "$5"
