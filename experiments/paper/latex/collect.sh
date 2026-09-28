#!/bin/sh
# Copies the generated figure data and table bodies from a results directory into the
# paper's layout (figures/evaluation/{data,tables}), which the TikZ files and floats.tex read.
# Usage: sh collect.sh <results-dir> [<out-dir>]   (default out-dir: this directory)
set -eu
R=${1:?results directory, e.g. experiments/results-paper}
O=${2:-$(dirname "$0")}
H=$R/headline_5turns
D=$O/figures/evaluation/data
T=$O/figures/evaluation/tables

mkdir -p "$D/headline_5turns/headline-a" "$D/headline_5turns/headline-b" "$D/precision_5turns" "$T"
for s in a b; do
  # CORALean's set: IEEE binary64, into the slot the paper's TikZ names
  cp "$H/headline-$s/ieee-binary64-paper-ti-union.dat" "$D/headline_5turns/headline-$s/dyadic-binary64-paper-ti-union.dat"
  # the figure's CORA set: CORALean's round-to-nearest baseline, CORA's own arithmetic (no MATLAB)
  cp "$H/headline-$s/nearest-binary64-paper-ti-union.dat" "$D/headline_5turns/headline-$s/cora-paper-ti-union.dat"
done
cp "$H/simulate-paper.dat" "$D/headline_5turns/simulate-paper.dat"
cp "$H/headline-a/ieee-binary64-every1-x0.dat" "$D/headline_5turns/x0.dat"
cp "$R"/paper/precision_headline_5turns/*.dat "$D/precision_5turns/"
for f in nn_table mnist_table runtime_table_headline_5turns; do
  cp "$R/paper/$f.tex" "$T/$f.tex"
done
echo "collect.sh: copied figure data and table bodies into $O/figures/evaluation"
