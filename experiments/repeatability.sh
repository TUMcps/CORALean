#!/usr/bin/env bash
# Runs every experiment of the paper's Sec. 4 and rebuilds its figures and tables
# (numbers as in the paper of 28-September-2026):
#   lake exe cache get && lake build     # build CORALean (once)
#   sh experiments/repeatability.sh      # ~75 min; --smoke: Fig. 4 only, ~3 min; --dyadic: + ablation
# Output: experiments/results (or --out DIR); all floats in <out>/paper/paper_floats.pdf.
[ -n "${BASH_VERSION:-}" ] || exec bash "$0" "$@"  # `sh` may be dash; the rest is bash
set -euo pipefail
cd "$(dirname "$0")/.."

USAGE="usage: sh experiments/repeatability.sh [--out DIR] [--smoke] [--no-latex] [--dyadic]"
OUT=experiments/results; SMOKE=0; NO_LATEX=""; DYADIC=0
while [ $# -gt 0 ]; do
  case "$1" in
    --out) OUT=$2; shift ;;
    --smoke) SMOKE=1 ;;
    --no-latex) NO_LATEX=--no-latex ;;
    --dyadic) DYADIC=1 ;;
    --help) echo "$USAGE"; exit 0 ;;
    *) echo "$USAGE" >&2; exit 1 ;;
  esac
  shift
done

C=experiments/config/headline_5turns.json
bench() { lake exe bench "$@" --out "$OUT"; }
section() { SECTION=$1; echo "===== $1 ($(date +%T))"; }
trap 'echo "repeatability.sh: FAILED in $SECTION" >&2' ERR

# ===== Fig. 4 (Sec. 4.1): reachable sets, (a) recursive = headline-b, (b) wrapping-free = headline-a =====
section "Fig. 4"  # IEEE binary64 (p=64), and round-to-nearest, which gives the figure's CORA set
for scheme in headline-b headline-a; do
  bench $scheme --config $C --type ieee --format binary64
  bench $scheme --config $C --type nearest --format binary64
done
if [ $SMOKE = 1 ]; then
  bash experiments/paper/make_paper.sh "$OUT" --no-latex
  echo "repeatability.sh: done (--smoke): headline figure data in $OUT/headline_5turns; the PDF needs the full run"
  exit 0
fi

# ===== Fig. 5 (Sec. 4.2): error radius over the steps, p = 4, 8, 16, 32, 64 =====
section "Fig. 5"
for format in binary4 binary8 binary16 binary32 binary64; do  # binary8 = E4M3, binary4 = E2M1
  bench exp2-timepoint --config $C --type ieee --format $format
done

# ===== Tab. 2 (Sec. 4.2): the toy network =====
section "Tab. 2"
bench nn-float32 --reps 11

# ===== Tab. 3 (Sec. 4.2): the MNIST networks, 100 images each (~50 min) =====
section "Tab. 3"
for net in small medium large; do
  for format in binary16 binary32 binary64; do
    bench nn-mnist --net $net --type ieee --format $format
  done
  bench nn-mnist --net $net --type hardware
done

# ===== Tab. 4 (Sec. 4.2): runtimes, Lean interpreter vs compiled C =====
section "Tab. 4"
bash experiments/run_runtime.sh --out "$OUT" --config $C
# The one number not computed here: the MATLAB column, CORA's stored runtimes (results/cora).
if git rev-parse -q --verify origin/results/cora >/dev/null 2>&1; then
  git archive origin/results/cora experiments/results-paper/headline_5turns | tar -x --strip-components=2 -C "$OUT"
else
  echo "repeatability.sh: origin/results/cora not available, the runtime table's MATLAB column stays empty"
fi

# ===== Ablation (--dyadic): Fig. 4, Fig. 5 and Tab. 3 at Dyadic, the same widths, no exponent bound =====
if [ $DYADIC = 1 ]; then
  section "Dyadic ablation"
  for scheme in headline-b headline-a; do bench $scheme --config $C --type dyadic --format binary64; done
  for format in binary4 binary8 binary16 binary32 binary64; do bench exp2-timepoint --config $C --type dyadic --format $format; done
  for net in small medium large; do for format in binary16 binary32 binary64; do bench nn-mnist --net $net --type dyadic --format $format; done; done
fi

# ===== First step under many number formats (qualitative figure): R_0 and X_1 =====
section "firststep"  # the flint runs (= Dyadic bit for bit) need the optional bench-flint, skipped without it
bench firststep --in experiments/firststep/configs.json
if [ -f .lake/flint/libcoralean_flint.a ]; then
  lake exe bench-flint firststep --in experiments/firststep/configs.json --out "$OUT"
else
  echo "repeatability.sh: FLINT shim not built, skipping the flint runs (README, \"FLINT backend\")"
fi

# ===== Formalization statistics (the figure on how much of CORA is formalized, and where the papers were wrong) =====
section "formalization-stats"  # reads references/, needs no build and no results; writes experiments/paper/
python3 scripts/check-references.py
python3 scripts/formalization-stats.py

# ===== All figures and tables -> paper_floats.pdf =====
section paper_floats.pdf
bash experiments/paper/make_paper.sh "$OUT" $NO_LATEX
echo "repeatability.sh: done: tables in $OUT/paper/*.tex, all floats in $OUT/paper/paper_floats.pdf"
echo "  (the figure's CORA set is CORALean's round-to-nearest run, within 2e-5 of CORA's MATLAB result)"
