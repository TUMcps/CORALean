# Paper figures and tables

Renders the evaluation floats of the paper (Fig. 4-5, Tab. 2-4) from the generated results,
with the paper's own TikZ files, table headers and captions (verbatim copies).

```
sh experiments/paper/latex/collect.sh experiments/results-paper   # results -> figures/evaluation/{data,tables}
cd experiments/paper/latex && latexmk -pdf paper_floats.tex      # -> paper_floats.pdf
```

`collect.sh` lays the generated files out exactly as in the paper repository
(`figures/evaluation/data`, `figures/evaluation/tables`); `floats.tex` and the TikZ files read them from there.
The headline figure's CORA set (`cora-paper-ti-union.dat`) is CORALean's round-to-nearest run
(`nearest-binary64`), so no MATLAB data is needed for it.
Requires a TeX Live with `llncs`, `pgfplots`, `siunitx`, `nicefrac`, `booktabs`, `cleveref`; `cora-macs.sty` is included.

## Via `make_paper.sh`

`experiments/paper/make_paper.sh [RESULTS_DIR] [--no-latex]` runs this
bundle for you, as its own last step: it copies this directory into
`<RESULTS_DIR>/paper-latex/`, runs `collect.sh` there, compiles
`paper_floats.tex` (local `latexmk -pdf`, else 3x local `pdflatex`, else a
pinned, dated `docker run texlive/texlive:...` image, else it fails with a
clear message rather than skipping or faking the PDF), and copies the result
to `<RESULTS_DIR>/paper/paper_floats.pdf`. `--no-latex` skips this whole
step (the figure `.dat`s and table `.tex`s above are still written). If
`<RESULTS_DIR>/paper-tree-expected/` exists (the committed snapshot of this
collected `figures/evaluation/` tree, at `results/paper`), it also
`diff -r`s it against the freshly collected tree and fails on any
difference. See `experiments/README.md`'s "`experiments/paper/make_paper.sh`"
section for the full command sequence from a results directory to
`paper_floats.pdf`.

## The formalization figure and appendix

`figures/formalization/formalization.tikz` (and a plain `formalization.svg` preview),
`figures/formalization/formalization-classes.tikz` and `appendix-formalization.tex` are not made
from a results directory: `scripts/formalization-stats.py` writes them, and
`experiments/paper/formalization-stats.json` beside the paper's scripts, from the tables under
`references/` and the Lean sources. `floats.tex` includes the first as `fig:formalization`;
`paper_floats.tex` inputs the appendix after the floats. Regenerate after any change to a table:

```
python3 scripts/formalization-stats.py          # JSON, .tikz, .svg and appendix
python3 scripts/formalization-stats.py --check  # fails when any of them is stale
python3 scripts/check-references.py             # the tables themselves, and the JSON
```

`repeatability.sh` runs the two scripts in its `formalization-stats` section, and CI runs both
checks. There are three counts, and the figure has one pgfplots panel for each (stacked horizontal
bars, as the evaluation figures: (a) CORA methods, (b) paper results, (c) Lean theorems). Panels rather than a side table: all three are counts of one kind, and
read at a glance as bars, with the exact numbers in the JSON and the appendix.

**1. CORA coverage** (`references/coverage/`, see its README). The unit is one CORA method file.
One bar per group of CORA classes: `contSet`, `contDynamics` (continuous- and discrete-time
systems, parameter systems, ARX, neural-network controlled systems), *Hybrid systems*
(`hybridDynamics/`) and *Neural networks* (`nn/@neuralNetwork` and the layer files). The segments
are the method states: `float` (a real-layer definition with a theorem, and a float-layer
computable definition with an outer or inner theorem), `proved` at the real layer only (the float
backlog, `needs_float` in the JSON), and not yet. Methods out of scope are not drawn; their count is the grey number after the bar (by reason, it is in
the JSON). There is no *Other* bar: what is left of
CORA (`global/`, `matrixSet/`, `specification/`, `discrDynamics/`, `converter/`) is a mixture
with no common unit, and is not tabulated.

**2. Theorem categories** (mechanical, no table). Every public `theorem`/`lemma` declaration under
`src/CORALean`, in exactly one category; a theorem takes the first that applies:

| Category | Meaning |
|---|---|
| float refinements | a `Float/` path, or `Float` in the declaration or file name, even if a paper row links it |
| proof helpers | `aux_*` names, the project's convention for a proof's own steps |
| paper theorems | anything else in a Lean file some row of `references/<year>/` links (the same parser that counts the paper results) |
| lemmas | every other public theorem |

`Examples/` theorems are not classified: they are counted apart (`examples` in the JSON) and are
not in the bar. The proof helpers are drawn, in light grey, so the four categories add up to the total.

**3. Paper results**, per paper and in total in the JSON, and per CORA class: each formalized row
is attributed to the class of the first Lean file it links (the mapping is in the coverage README,
and `bucket` in `scripts/check-references.py`; files on no CORA class land in `global` or
`specification`, `Examples/` in `examples`). The figure draws the totals:

| Class | Meaning |
|---|---|
| `correct` | formalized as printed |
| `underspecified` | not false, but a hypothesis, definition or index is missing or misprinted (a typo, an implicit `h ≥ 0`, a missing non-emptiness) and the formalization supplies it |
| `proof-gap` | the statement is formalized as printed, but the printed proof or derivation does not establish it: a false intermediate step, an unstated lemma, an argument that only holds one way |
| `fixed` | false, or ill-defined, as printed, and true after the correction the row names (an added hypothesis, a changed constant, a reversed condition); formalized in the corrected form |
| `false` | false as printed and not repairable in the paper's intent (a counterexample is formalized or the claim is dropped); none so far |

`proof-gap` is not one of the four first proposed: the pages record it more often than `fixed`
(the proof is wrong, the claim stands), and folding it into either neighbour would overstate or
hide a mistake. Algorithm listings (`Alg. n`, `Heuristic`) are read as intentionally simplified; a correction there counts as `underspecified`. A row takes the most severe class that applies. Rows outside the count carry the
README's own five reasons instead (`restated`, `mathlib`, `not-a-claim`, `done-differently`,
`not-covered`), and a row in scope and not yet formalized is `—`.

**The appendix** (`appendix-formalization.tex`) is two figures, no table: `formalization-classes.tikz`,
one bar per CORA class in the three method segments, grouped under italic group headings, with the
out-of-scope count after the bar; and `formalization-findings.tikz`, the paper findings
(underspecified, proof gap, fixed, false) per group. The number of methods where CORA itself is
wrong and CORALean parts from it deliberately (`cora-issue` notes) is in the JSON (`cora_issues`).
There is no TeX Live where the generator runs, so these files are written to the same pgfplots
and `booktabs` forms as the evaluation floats and have not been compiled by it.

Not counted: which paper *results* also have a float refinement. Nothing in a row says so, float
files rarely cite the paper they refine, and matching `Real/` to `Float/` files by name finds
counterparts without a theorem and misses ones with one, so any number would be a guess. (For CORA
*methods* the coverage tables do say so: that is `float` against `proved`.)
