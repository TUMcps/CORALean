#!/usr/bin/env bash
# run_runtime.sh -- the number-type runtime ablation on headline_default:
# schemes headline-a and headline-b, each at five backends --
#   * Dyadic binary64, compiled (`lake exe bench`)
#   * native Float, compiled
#   * round-to-nearest `NearestFloat`, compiled (`--type nearest`: the unsound
#     CORA-style baseline, what directed rounding costs against it)
#   * Dyadic binary64, interpreter (`lake env lean --run`)
#   * native Float, interpreter
# -- ten runs, `medianNs` read back from each run's own JSON (the same
# median-over-`--reps` `Timing.lean` computes), into one runtime.csv/.json
# table under `<out>/headline_default/runtime/`.
#
# `--cold-build` additionally times a cold build of the bench executable's
# OWN modules: it touches `src/CORALean/Examples/Bench/*.lean` (and the root
# `Bench.lean`) so lake considers only those stale, then times `lake build
# bench` -- Mathlib and every other library stay cached, so this is not a
# whole-tree rebuild.
#
# bash, for `set -o pipefail`; run from anywhere, it cd's to the repository
# root itself.

set -euo pipefail

cd "$(dirname "$0")/.."

OUT_DIR="${BENCH_OUT_DIR:-experiments/results}"
REPS=3
CONFIG="experiments/config/headline_default.json"
COLD_BUILD=0
BENCH_ROOT="src/CORALean/Examples/Bench.lean"

while [ $# -gt 0 ]; do
  case "$1" in
    --out) OUT_DIR="$2"; shift 2 ;;
    --reps) REPS="$2"; shift 2 ;;
    --cold-build) COLD_BUILD=1; shift ;;
    *) echo "usage: run_runtime.sh [--out DIR] [--reps N] [--cold-build]" >&2; exit 1 ;;
  esac
done

RUNTIME_DIR="$OUT_DIR/headline_default/runtime"
mkdir -p "$RUNTIME_DIR"
CSV="$RUNTIME_DIR/runtime.csv"
JSON_OUT="$RUNTIME_DIR/runtime.json"

echo "scheme,backend,number_type,medianNs" > "$CSV"
rows_json="[]"

# Appends one row to both the CSV and the accumulated JSON array -- `medianNs`
# is read out of the run's own JSON, not re-timed here.
record() {
  local scheme="$1" backend="$2" numtype="$3" json_path="$4" medianNs
  medianNs=$(python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['meta']['medianNs'])" \
    "$json_path")
  echo "$scheme,$backend,$numtype,$medianNs" >> "$CSV"
  rows_json=$(python3 -c "
import json, sys
rows = json.loads(sys.argv[1])
rows.append({'scheme': sys.argv[2], 'backend': sys.argv[3], 'number_type': sys.argv[4],
             'medianNs': int(sys.argv[5])})
print(json.dumps(rows))
" "$rows_json" "$scheme" "$backend" "$numtype" "$medianNs")
}

cold_build_ns=""
if [ "$COLD_BUILD" -eq 1 ]; then
  echo "== cold build (bench's own modules only) =="
  touch src/CORALean/Examples/Bench/*.lean src/CORALean/Examples/Bench.lean
  t0=$(date +%s%N)
  lake build bench
  t1=$(date +%s%N)
  cold_build_ns=$((t1 - t0))
  echo "cold build: ${cold_build_ns} ns"
else
  lake build bench >/dev/null
fi

for scheme in headline-a headline-b; do
  lake exe bench "$scheme" --type dyadic --format binary64 --config "$CONFIG" --reps "$REPS" \
    --out "$RUNTIME_DIR/compiled-dyadic"
  record "$scheme" compiled dyadic-binary64 \
    "$RUNTIME_DIR/compiled-dyadic/headline_default/$scheme/dyadic-binary64.json"

  lake exe bench "$scheme" --type float --config "$CONFIG" --reps "$REPS" \
    --out "$RUNTIME_DIR/compiled-float"
  record "$scheme" compiled float \
    "$RUNTIME_DIR/compiled-float/headline_default/$scheme/float.json"

  lake exe bench "$scheme" --type nearest --config "$CONFIG" --reps "$REPS" \
    --out "$RUNTIME_DIR/compiled-nearest"
  record "$scheme" compiled nearest-binary64 \
    "$RUNTIME_DIR/compiled-nearest/headline_default/$scheme/nearest-binary64.json"

  lake env lean --run "$BENCH_ROOT" "$scheme" --type dyadic --format binary64 --config "$CONFIG" \
    --reps "$REPS" --out "$RUNTIME_DIR/interp-dyadic"
  record "$scheme" interpreter dyadic-binary64 \
    "$RUNTIME_DIR/interp-dyadic/headline_default/$scheme/dyadic-binary64.json"

  lake env lean --run "$BENCH_ROOT" "$scheme" --type float --config "$CONFIG" \
    --reps "$REPS" --out "$RUNTIME_DIR/interp-float"
  record "$scheme" interpreter float \
    "$RUNTIME_DIR/interp-float/headline_default/$scheme/float.json"
done

python3 -c "
import json, sys
rows = json.loads(sys.argv[1])
doc = {'rows': rows}
if sys.argv[2]:
    doc['coldBuildNs'] = int(sys.argv[2])
json.dump(doc, open(sys.argv[3], 'w'), indent=2)
" "$rows_json" "$cold_build_ns" "$JSON_OUT"

echo "run_runtime: wrote $CSV and $JSON_OUT"
