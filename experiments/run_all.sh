#!/bin/sh
# One-command reproduction of every CORALean-side experiment, at every
# type/precision each experiments/config/headline_*.json asks for, followed by
# the plotting pass. Uses the interpreter backend (`lake env lean --run`), not
# `lake exe bench`, so this needs only a built tree (`lake exe cache get &&
# lake build`), no link step.
#
# CORA/MATLAB runs are a separate, documented step -- see
# experiments/README.md's "CORA" section -- since they need MATLAB and a
# checked-out CORA on the path, neither of which this script can assume.
#
# POSIX sh, run from anywhere; it cd's to the repository root itself.

set -eu

cd "$(dirname "$0")/.."

OUT_DIR="${BENCH_OUT_DIR:-experiments/results}"
EXPERIMENTS="dtdemo headline-a headline-b exp2-timepoint"
BENCH_ROOT="src/CORALean/Examples/Bench.lean"

for config in experiments/config/headline_*.json; do
  [ -f "$config" ] || continue
  echo "== $config =="
  # `precisions` is read with python3 rather than a shell JSON parser, since
  # python3 is already this harness's one plotting dependency and nothing
  # else here needs jq or similar on the artifact evaluator's image.
  combos=$(python3 -c '
import json, sys
cfg = json.load(open(sys.argv[1]))
for p in cfg["precisions"]:
    print("dyadic " + p["format"] if p["type"] == "dyadic" else "float -")
' "$config")
  echo "$combos" | while IFS=' ' read -r ty format; do
    for exp in $EXPERIMENTS; do
      if [ "$ty" = "dyadic" ]; then
        label="dyadic --format $format"
        set +e
        lake env lean --run "$BENCH_ROOT" "$exp" --type dyadic --format "$format" \
          --config "$config" --out "$OUT_DIR"
        status=$?
        set -e
      else
        label="float"
        set +e
        lake env lean --run "$BENCH_ROOT" "$exp" --type float \
          --config "$config" --out "$OUT_DIR"
        status=$?
        set -e
      fi
      if [ "$status" -ne 0 ]; then
        echo "  ($exp at $label: not available yet, status $status)"
      fi
    done
  done
done

echo "== plotting =="
find "$OUT_DIR" -name '*.json' | while IFS= read -r run; do
  python3 experiments/plot/to_pgfplots.py "$run" "${run%.json}-plot"
done

echo "run_all: done -- results and plot data under $OUT_DIR"
