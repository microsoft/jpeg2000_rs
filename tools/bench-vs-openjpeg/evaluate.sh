#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -lt 5 ] || [ "$#" -gt 6 ]; then
    echo "usage: bash evaluate.sh OUTPUT OPENJPEG_SOURCE C2_SOURCE C12_SOURCE CPU [NUMERICAL_299]" >&2
    exit 2
fi

here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mkdir -- "$1"
output=$(cd -- "$1" && pwd)
numerical=()
if [ "$#" -eq 6 ]; then
    numerical=(--numerical-299 "$6")
fi

echo "Measuring baseline"
python3 "$here/run.py" --output "$output/baseline" --openjpeg-source "$2" \
    --configs generic,consumer,native --cpu "$5"
echo "Measuring isolated C2"
python3 "$here/compare.py" --baseline "$output/baseline" --candidate-source "$3" \
    --output "$output/c2" --cpu "$5" "${numerical[@]}"
echo "Measuring isolated C12"
python3 "$here/compare.py" --baseline "$output/baseline" --candidate-source "$4" \
    --output "$output/c12" --cpu "$5" "${numerical[@]}"
echo "Collecting separate profiles and counters"
python3 "$here/profile_baseline.py" --baseline "$output/baseline" \
    --output "$output/profiles" --perf "${PERF:-perf}" --cpu "$5"
for reduce in 1 2 3; do
    python3 "$here/run.py" --output "$output/reduce-$reduce" --openjpeg-source "$2" \
        --reuse-builds "$output/baseline" --configs generic \
        --case '^noisy-gray-(lossless|lossy)-j2k$' --reduce "$reduce" --cpu "$5"
done
python3 "$here/run.py" --output "$output/window" --openjpeg-source "$2" \
    --reuse-builds "$output/baseline" --configs generic \
    --case '^noisy-gray-(lossless|lossy)-j2k$' --window 128,128,512,512 --cpu "$5"
echo "Available matrix complete: $output"
