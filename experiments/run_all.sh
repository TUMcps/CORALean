#!/usr/bin/env bash
# One-command reproduction of the paper's headline runs, for every
# experiments/config/headline_*.json (or one, with `--config`): headline-a
# and headline-b at dyadic binary64, float and the unsound round-to-nearest
# baseline (`--type nearest`, binary64), exp2-timepoint at every dyadic format
# and at every round-to-nearest one (the precision ablation) -- then the plotting pass
# (to_pgfplots.py --merged) and simulate.py. Also one nn-float32 run.
# `dtdemo` (the placeholder Euler discretization, not a paper result) is not
# part of this sweep; `lake exe bench dtdemo ...` still runs it directly.
#
# Compiled by default (`lake exe bench`), matching the paper's own reported
# timings -- the interpreter (`lake env lean --run`, no link step, only a
# built tree needed) is 4-7x slower and is `--interp`/`BENCH_BACKEND=interp`,
# for a quick check without paying `lake exe`'s link cost. `--config FILE`
# restricts the sweep to one config instead of every `headline_*.json`;
# `--reps N` overrides every config's own `reps`, for a quick smoke test.
#
# A run whose own JSON reports `"status": "none"` (an inadmissible Taylor
# order, or a genuine blow-up saturating to `Infinity`/`NaN`) is a legitimate
# result, reported and not a failure -- decided and documented in
# experiments/README.md's "run_all.sh" section. Anything else nonzero (a
# crash: a bad config, an uncaught exception, ...) is a genuine failure: it
# is reported, the sweep keeps going, and the script itself exits nonzero at
# the very end, listing every one, so a broken run is never silently lost in
# the log.
#
# CORA/MATLAB runs are a separate, documented step -- see
# experiments/README.md's "CORA" section -- since they need MATLAB and a
# checked-out CORA on the path, neither of which this script can assume.
#
# bash, for `set -o pipefail` and arrays; run from anywhere, it cd's to the
# repository root itself.

set -euo pipefail

cd "$(dirname "$0")/.."

OUT_DIR="${BENCH_OUT_DIR:-experiments/results}"
BACKEND="${BENCH_BACKEND:-compiled}"
BENCH_ROOT="src/CORALean/Examples/Bench.lean"
PRECISION_FORMATS="binary4 binary8 binary16 binary32 binary64"
CONFIG_FILTER=""
REPS_OVERRIDE=""

while [ $# -gt 0 ]; do
  case "$1" in
    --interp) BACKEND="interp"; shift ;;
    --config) CONFIG_FILTER="$2"; shift 2 ;;
    --reps) REPS_OVERRIDE="$2"; shift 2 ;;
    *)
      echo "usage: run_all.sh [--interp] [--config FILE] [--reps N]" >&2
      exit 1
      ;;
  esac
done

# Appended to every `bench_run` call -- empty (the config's own `reps`) unless
# `--reps` overrode it, e.g. for a quick `--reps 1` smoke test.
REPS_ARGS=()
if [ -n "$REPS_OVERRIDE" ]; then
  REPS_ARGS=(--reps "$REPS_OVERRIDE")
fi

FAILED_RUNS=()

# `lake exe bench` (compiled, the default -- the paper's own timings) or
# `lake env lean --run` (`--interp`/`BENCH_BACKEND=interp`), same arguments.
bench_run() {
  if [ "$BACKEND" = "interp" ]; then
    lake env lean --run "$BENCH_ROOT" "$@"
  else
    lake exe bench "$@"
  fi
}

# Runs "$@" (a `bench_run` or a plotting/simulation call), reporting a
# nonzero exit: a `"status: none"` line in the run's own output (`aux_runTiTp`
# prints one whenever it writes `"status": "none"`) is a legitimate result,
# not added to `FAILED_RUNS`; anything else nonzero is, and fails the script
# at the end -- see the module docstring.
run_experiment() {
  local desc="$1"; shift
  local out status
  set +e
  out=$("$@" 2>&1)
  status=$?
  set -e
  printf '%s\n' "$out"
  if [ "$status" -ne 0 ]; then
    if printf '%s' "$out" | grep -q 'status: none'; then
      echo "  ($desc: a legitimate \"status: none\" result, see the reason above)"
    else
      echo "  ($desc: FAILED, status $status)"
      FAILED_RUNS+=("$desc (status $status)")
    fi
  fi
}

echo "== nn-float32 =="
run_experiment "nn-float32" bench_run nn-float32 --reps 11 --out "$OUT_DIR"

if [ -n "$CONFIG_FILTER" ]; then
  configs="$CONFIG_FILTER"
else
  configs="experiments/config/headline_*.json"
fi

for config in $configs; do
  [ -f "$config" ] || continue
  echo "== $config =="

  # headline-a / headline-b: the headline pair, dyadic binary64, float and the
  # round-to-nearest baseline (NO guarantee, as in CORA)
  for exp in headline-a headline-b; do
    run_experiment "$config $exp dyadic binary64" bench_run "$exp" --type dyadic \
      --format binary64 --config "$config" --out "$OUT_DIR" "${REPS_ARGS[@]}"
    run_experiment "$config $exp float" bench_run "$exp" --type float \
      --config "$config" --out "$OUT_DIR" "${REPS_ARGS[@]}"
    run_experiment "$config $exp nearest binary64" bench_run "$exp" --type nearest \
      --config "$config" --out "$OUT_DIR" "${REPS_ARGS[@]}"
  done

  # exp2-timepoint: the precision ablation, every format binary4..binary64, both
  # outward-rounded (dyadic) and round-to-nearest (nearest, the unsound baseline)
  for format in $PRECISION_FORMATS; do
    run_experiment "$config exp2-timepoint dyadic $format" bench_run exp2-timepoint \
      --type dyadic --format "$format" --config "$config" --out "$OUT_DIR" "${REPS_ARGS[@]}"
    run_experiment "$config exp2-timepoint nearest $format" bench_run exp2-timepoint \
      --type nearest --format "$format" --config "$config" --out "$OUT_DIR" "${REPS_ARGS[@]}"
  done
done

echo "== plotting =="
while IFS= read -r run; do
  run_experiment "plot $run" python3 experiments/plot/to_pgfplots.py "$run" \
    "${run%.json}-plot" --merged
done < <(find "$OUT_DIR" -name '*.json')

echo "== simulation =="
for config in $configs; do
  [ -f "$config" ] || continue
  name=$(basename "$config" .json)
  run_experiment "simulate $config" python3 experiments/plot/simulate.py "$config" \
    "$OUT_DIR/$name/simulate.dat"
done

if [ "${#FAILED_RUNS[@]}" -gt 0 ]; then
  echo "run_all: FAILED (${#FAILED_RUNS[@]} run(s)):"
  printf '  %s\n' "${FAILED_RUNS[@]}"
  exit 1
fi

echo "run_all: done -- results and plot data under $OUT_DIR"
