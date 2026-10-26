#!/usr/bin/env bash
# All three converted `mnistfc` networks (small/medium/large) at every
# precision this harness supports: dyadic binary4..binary64, native `Float`,
# and (once `--type nearest` is on the tree) the unsound round-to-nearest
# baseline at the same formats -- `nn-mnist`'s own ablation, the MNIST
# counterpart of `run_all.sh`'s `exp2-timepoint` sweep.
#
# Compiled by default (`lake exe bench`); `--interp`/`BENCH_BACKEND=interp`
# switches to the interpreter. `--images K` overrides the default 100 (a
# quick `--images 10` smoke test costs a fraction of a full run); `--reps N`
# repeats each image's propagation for a steadier median time; `--net NAME`
# restricts the sweep to one network instead of all three.
#
# A run's own nonzero exit (a bad `--net`, a crash) is a genuine failure,
# reported and the sweep keeps going, failing the script itself at the end
# -- the same discipline `run_all.sh` documents; `-e` stays off so `run_one`
# can catch that exit itself instead of the shell exiting under it.

set -uo pipefail

cd "$(dirname "$0")/../../.."

OUT_DIR="${BENCH_OUT_DIR:-experiments/results}"
BACKEND="${BENCH_BACKEND:-compiled}"
BENCH_ROOT="src/CORALean/Examples/Bench.lean"
PRECISION_FORMATS="binary4 binary8 binary16 binary32 binary64"
NETS="small medium large"
IMAGES=""
REPS_OVERRIDE=""

while [ $# -gt 0 ]; do
  case "$1" in
    --interp) BACKEND="interp"; shift ;;
    --net) NETS="$2"; shift 2 ;;
    --images) IMAGES="$2"; shift 2 ;;
    --reps) REPS_OVERRIDE="$2"; shift 2 ;;
    *)
      echo "usage: run_mnist.sh [--interp] [--net small|medium|large] [--images K] [--reps N]" >&2
      exit 1
      ;;
  esac
done

IMAGES_ARGS=()
[ -n "$IMAGES" ] && IMAGES_ARGS=(--images "$IMAGES")
REPS_ARGS=()
[ -n "$REPS_OVERRIDE" ] && REPS_ARGS=(--reps "$REPS_OVERRIDE")

FAILED_RUNS=()

bench_run() {
  if [ "$BACKEND" = "interp" ]; then
    lake env lean --run "$BENCH_ROOT" "$@"
  else
    lake exe bench "$@"
  fi
}

run_one() {
  local desc="$1"; shift
  if ! "$@"; then
    echo "  ($desc: FAILED)"
    FAILED_RUNS+=("$desc")
  fi
}

# `--type nearest`: round-to-nearest, as CORA itself computes, NO soundness
# guarantee -- run only for the "round-to-nearest (as in CORA)" comparison
# column, skipped automatically if this tree predates it.
HAVE_NEAREST=0
if bench_run nn-mnist --net small --type nearest --images 1 --out /tmp/nn-mnist-nearest-check \
    >/dev/null 2>&1; then
  HAVE_NEAREST=1
else
  echo "(--type nearest not on this tree, skipping the round-to-nearest column)"
fi

for net in $NETS; do
  echo "== $net =="
  for format in $PRECISION_FORMATS; do
    run_one "$net dyadic $format" bench_run nn-mnist --net "$net" --type dyadic \
      --format "$format" --out "$OUT_DIR" "${IMAGES_ARGS[@]}" "${REPS_ARGS[@]}"
    if [ "$HAVE_NEAREST" -eq 1 ]; then
      run_one "$net nearest $format" bench_run nn-mnist --net "$net" --type nearest \
        --format "$format" --out "$OUT_DIR" "${IMAGES_ARGS[@]}" "${REPS_ARGS[@]}"
    fi
  done
  run_one "$net hardware" bench_run nn-mnist --net "$net" --type hardware \
    --out "$OUT_DIR" "${IMAGES_ARGS[@]}" "${REPS_ARGS[@]}"
done

if [ "${#FAILED_RUNS[@]}" -gt 0 ]; then
  echo "run_mnist: FAILED (${#FAILED_RUNS[@]} run(s)):"
  printf '  %s\n' "${FAILED_RUNS[@]}"
  exit 1
fi

echo "run_mnist: done -- results under $OUT_DIR/nn-mnist"
