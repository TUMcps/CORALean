#!/usr/bin/env bash
# make_paper.sh -- from an existing results directory (arg, default
# experiments/results-paper), regenerates every figure .dat file and every
# table body the paper `\input`s, into `<results>/paper/`.
#
# Figure data (experiments/README.md's "Plotting" section, `to_pgfplots.py`/
# `simulate.py`): for every config x {headline-a, headline-b} x {dyadic
# binary64, float, nearest, cora} run this results directory holds, a merged
# tube (ti and tp) at `--every 1` and again at `--every 10` (thinned), plus
# `-x0.dat` and the per-step hull `.dat`; one simulation-trajectory `.dat` per
# config. Then `gen_figures.py` (beside this script): an `-eradius.dat` at
# dyadic binary64 and float, a `-paper-ti-union.dat` at every type (every
# step's polygon unioned, no thinning -- needs `shapely`, see below), and
# one `simulate-paper.dat` per config (its own docstrings say the exact rule
# each follows). `experiments/results-paper/README.md` documents the exact
# naming scheme all of this writes.
#
# `shapely` (pinned in experiments/paper/requirements.txt) is required for
# `-paper-ti-union.dat`: this script checks it is importable before doing
# anything else and FAILS with a clear message if it is not (no silent
# skip) -- `python3 -m venv .venv && .venv/bin/pip install -r
# experiments/paper/requirements.txt`, or `pip install --user -r
# experiments/paper/requirements.txt`.
#
# Table bodies (`gen_tables.py`, a standard-library Python helper beside this
# script): the booktabs bodies `experiments/README.md`'s callers expect --
# headline_table (plus its per-config and long-format siblings), precision_table,
# nn_table, runtime_table (per config), nearest_vs_cora -- plus the precision
# ablation's per-step error-radius `.dat` files. Then `mnist_table.py`, the
# same idea over `<results>/nn-mnist/` (skipped, not a failure, if that
# directory does not exist): mnist_table.{tex,csv} and mnist_nets.csv. All
# under `<results>/paper/`.
#
# PNG rendering (`render_png.py`, optional): only if `matplotlib` is
# importable, which it is not on this harness's own image -- skipped with a
# message rather than failing the script.
#
# Every per-run JSON this reads may be gzipped (`<run>.json.gz`, written once
# a results directory crosses check-conventions.sh's/the artifact's own size
# budget -- see experiments/results-paper/README.md) or plain; both
# `to_pgfplots.py` and `gen_tables.py`'s `common.load_json` read either.
#
# bash, for `set -o pipefail`; run from anywhere, it cd's to the repository
# root itself (two directories up from this file).
#
# Usage:
#     experiments/paper/make_paper.sh [RESULTS_DIR]

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR/../.."

RESULTS_DIR="${1:-experiments/results-paper}"
TO_PGFPLOTS="experiments/plot/to_pgfplots.py"
SIMULATE="experiments/plot/simulate.py"
GEN_FIGURES="$SCRIPT_DIR/gen_figures.py"

if [ ! -d "$RESULTS_DIR" ]; then
  echo "make_paper: no such results directory: $RESULTS_DIR" >&2
  exit 1
fi

if ! python3 -c 'import shapely' >/dev/null 2>&1; then
  echo "make_paper: shapely is required (for -paper-ti-union.dat) and is not" >&2
  echo "  importable -- pip install -r experiments/paper/requirements.txt, or" >&2
  echo "  python3 -m venv .venv && .venv/bin/pip install -r experiments/paper/requirements.txt" >&2
  exit 1
fi

TYPES="dyadic-binary64 float nearest-binary64 cora"
SCHEMES="headline-a headline-b"

echo "== figure data: $RESULTS_DIR =="
for config_dir in "$RESULTS_DIR"/*/; do
  config=$(basename "$config_dir")
  [ "$config" = "nn" ] && continue
  [ "$config" = "nn-mnist" ] && continue
  [ "$config" = "paper" ] && continue

  for scheme in $SCHEMES; do
    scheme_dir="$config_dir$scheme"
    [ -d "$scheme_dir" ] || continue
    for type in $TYPES; do
      run_json="$scheme_dir/$type.json"
      [ -f "$run_json" ] || run_json="$scheme_dir/$type.json.gz"
      [ -f "$run_json" ] || continue
      for every in 1 10; do
        python3 "$TO_PGFPLOTS" "$run_json" "$scheme_dir/$type-every$every" \
          --every "$every" --merged
      done
      python3 "$GEN_FIGURES" paper-ti-union "$RESULTS_DIR" "$config" "$scheme" "$type"
      case "$type" in
        dyadic-binary64|float)
          python3 "$GEN_FIGURES" eradius "$RESULTS_DIR" "$config" "$scheme" "$type" ;;
      esac
    done
  done

  config_json="experiments/config/$config.json"
  if [ -f "$config_json" ]; then
    python3 "$SIMULATE" "$config_json" "$config_dir/simulate.dat"
    python3 "$GEN_FIGURES" simulate-paper "$RESULTS_DIR" "$config" "$config_json"
  fi
done

echo "== tables =="
python3 "$SCRIPT_DIR/gen_tables.py" "$RESULTS_DIR"
python3 "$SCRIPT_DIR/mnist_table.py" "$RESULTS_DIR"

echo "== PNG rendering (optional) =="
if python3 -c 'import matplotlib' >/dev/null 2>&1; then
  python3 "$SCRIPT_DIR/render_png.py" "$RESULTS_DIR"
else
  echo "make_paper: matplotlib not importable, skipping render_png.py"
fi

echo "make_paper: done -- figure data and table bodies under $RESULTS_DIR/paper"
