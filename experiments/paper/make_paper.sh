#!/usr/bin/env bash
# make_paper.sh -- from an existing results directory (arg, default
# experiments/results-paper), regenerates every figure .dat file and every
# table body the paper `\input`s, into `<results>/paper/`.
#
# Figure data (experiments/README.md's "Plotting" section, `to_pgfplots.py`/
# `simulate.py`): for every config x {headline-a, headline-b} x {ieee
# binary64, dyadic binary64, hardware, nearest, cora} run this results directory holds, a merged
# tube (ti and tp) at `--every 1` and again at `--every 10` (thinned), plus
# `-x0.dat` and the per-step hull `.dat`; one simulation-trajectory `.dat` per
# config. Then `gen_figures.py` (beside this script): an `-eradius.dat` at
# ieee and dyadic binary64 and hardware, a `-paper-ti-union.dat` at every type (every
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
# ablation's per-step error-radius `.dat` files, and (if the config's
# `exp2-timepoint` directory exists) the precision ablation's own figure
# data under `precision_<config>/` (default config `headline_5turns`) plus
# its `precision_<config>.csv` summary. Then `mnist_table.py`, the
# same idea over `<results>/nn-mnist/` (skipped, not a failure, if that
# directory does not exist): mnist_table.{tex,csv} and mnist_nets.csv. All
# under `<results>/paper/`.
#
# PNG rendering (`render_png.py`, optional): only if `matplotlib` is
# importable, which it is not on this harness's own image -- skipped with a
# message rather than failing the script.
#
# Finally, `paper_floats.pdf` (skipped by `--no-latex`): `latex/collect.sh`
# assembles `<results>/paper-latex/` -- a copy of experiments/paper/latex/
# (the paper's own llncs driver, floats.tex, the TikZ files, cora-macs.sty)
# plus this run's own figures/evaluation/{data,tables}, laid out exactly as
# the paper repository -- then compiles paper_floats.tex there: `latexmk -pdf`
# or 3x `pdflatex` if a TeX Live is on PATH, else a pinned `docker run` of a
# dated `texlive/texlive` image if `docker` is on PATH, else this script
# fails with a message (never a faked/missing PDF). The compiled PDF is then
# copied to `<results>/paper/paper_floats.pdf`. If `<results>/
# paper-tree-expected/` exists (the committed snapshot of the paper's
# figures/evaluation/ tree, see experiments/results-paper/README.md), this
# also `diff -r`s it against the freshly collected figures/evaluation/ and
# fails on any difference -- a regression check that a rerun on the same
# results directory reproduces the same figures/tables byte for byte.
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
#     experiments/paper/make_paper.sh [RESULTS_DIR] [--no-latex]

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR/../.."

RESULTS_DIR="experiments/results-paper"
NO_LATEX=0
for arg in "$@"; do
  case "$arg" in
    --no-latex) NO_LATEX=1 ;;
    *) RESULTS_DIR="$arg" ;;
  esac
done
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

TYPES="ieee-binary64 dyadic-binary64 hardware nearest-binary64 cora"
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
        ieee-binary64|dyadic-binary64|hardware)
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

if [ "$NO_LATEX" -eq 1 ]; then
  echo "== paper_floats.pdf: skipped (--no-latex) =="
else
  echo "== paper_floats.pdf =="
  LATEX_SRC="$SCRIPT_DIR/latex"
  PAPER_BUILD="$RESULTS_DIR/paper-latex"
  # A pinned, dated TeX Live image -- never `:latest`, so a rebuild months
  # from now compiles against the same package set. Update deliberately.
  DOCKER_TEXLIVE_IMAGE="texlive/texlive:TL2025-historic"

  rm -rf "$PAPER_BUILD"
  mkdir -p "$PAPER_BUILD"
  cp -r "$LATEX_SRC"/. "$PAPER_BUILD"/
  sh "$LATEX_SRC/collect.sh" "$RESULTS_DIR" "$PAPER_BUILD"

  if command -v latexmk >/dev/null 2>&1; then
    echo "make_paper: compiling with local latexmk"
    ( cd "$PAPER_BUILD" && latexmk -pdf -interaction=nonstopmode -halt-on-error paper_floats.tex )
  elif command -v pdflatex >/dev/null 2>&1; then
    echo "make_paper: compiling with local pdflatex (3 passes, no latexmk on PATH)"
    ( cd "$PAPER_BUILD" && for _ in 1 2 3; do
        pdflatex -interaction=nonstopmode -halt-on-error paper_floats.tex
      done )
  elif command -v docker >/dev/null 2>&1; then
    echo "make_paper: no local TeX on PATH, compiling with docker ($DOCKER_TEXLIVE_IMAGE)"
    docker run --rm -v "$(cd "$PAPER_BUILD" && pwd):/work" -w /work "$DOCKER_TEXLIVE_IMAGE" \
      latexmk -pdf -interaction=nonstopmode -halt-on-error paper_floats.tex
  else
    echo "make_paper: cannot compile paper_floats.pdf -- no latexmk/pdflatex on PATH and no" >&2
    echo "  docker available. Install a TeX Live (llncs, pgfplots, siunitx, nicefrac," >&2
    echo "  booktabs, cleveref -- see experiments/paper/latex/README.md) or docker, or" >&2
    echo "  pass --no-latex to skip this step." >&2
    exit 1
  fi

  mkdir -p "$RESULTS_DIR/paper"
  cp "$PAPER_BUILD/paper_floats.pdf" "$RESULTS_DIR/paper/paper_floats.pdf"

  EXPECTED_TREE="$RESULTS_DIR/paper-tree-expected"
  if [ -d "$EXPECTED_TREE" ]; then
    echo "== tree check: $EXPECTED_TREE vs the freshly collected figures/evaluation/ =="
    if diff -r "$EXPECTED_TREE" "$PAPER_BUILD/figures/evaluation"; then
      echo "make_paper: tree check passed"
    else
      echo "make_paper: figures/evaluation/ differs from $EXPECTED_TREE -- see the diff above" >&2
      exit 1
    fi
  fi

  echo "make_paper: paper_floats.pdf -> $RESULTS_DIR/paper/paper_floats.pdf"
fi

echo "make_paper: done -- figure data and table bodies under $RESULTS_DIR/paper"
