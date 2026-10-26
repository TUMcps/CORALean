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

`figures/formalization/formalization.tikz` (and a plain `formalization.svg` preview), `appendix-errors.tex`,
`figures/formalization/formalization-classes-{sets,contdynamics,others}.tikz` and `appendix-formalization.tex` are not made
from a results directory: `scripts/formalization-stats.py` writes them, and
`experiments/paper/formalization-stats.json` beside the paper's scripts, from the tables under
`references/` and the Lean sources. `floats.tex` includes the first as `fig:formalization`;
`paper_floats.tex` inputs the appendix after the floats. Regenerate after any change to a table:

```
python3 scripts/formalization-stats.py          # JSON, .tikz, .svg, appendix and errors table
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
backlog, `needs_float` in the JSON), `bound` (a sound result looser than or different from CORA's, drawn as "sound bound only"), and not yet. Methods out of scope are not drawn; their count is the grey number after the bar (by reason, it is in
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

**The appendix** (`appendix-formalization.tex`) is four figures, no table: `formalization-classes-sets.tikz`,
`formalization-classes-contdynamics.tikz` and `formalization-classes-others.tikz` (split so each fits a page and
they float independently),
one bar per CORA class in the three method segments, grouped under italic group headings, with the
out-of-scope count after the bar; and `formalization-findings.tikz`, the paper findings
(underspecified, proof gap, fixed, false) per group. The number of methods where CORA itself is
wrong and CORALean parts from it deliberately (`cora-issue` notes) is in the JSON (`cora_issues`).
There is no TeX Live where the generator runs, so these files are written to the same pgfplots
and `booktabs` forms as the evaluation floats and have not been compiled by it.

**The errors table** (`appendix-errors.tex`) lists every paper result classed `false` or
`fixed`, one `longtable` row each (booktabs, `\footnotesize`): the `false` rows first, a rule, then
the `fixed` ones, each sorted by year, then page, then the row's place in the page's table. A row
holds the reference as `\cite[Prop.~32]{key}` (a dagger marks `false`) with a link `[Audit]` to the
result's page under `references/`, a few words on what is wrong, and links `[Cex]` to the Lean counterexample and
`[Fix]` to the Lean file proving the corrected statement (`---` where there is none: every
`false` row, and a `fixed` row whose corrected theorem lives in a file the row does not link).
`python3 scripts/formalization-stats.py` writes it with the files above, through
`scripts/paper/errors-table.py`, which documents how the two files are picked from the row's links.
It was compiled against `llncs` and `splncs04`. The data it needs that the ledger does not hold
is committed beside it:

* `experiments/paper/ledger-errors.json`: per page and result label (as printed in the row,
  without backticks), the description, written from the row's Class cell and the page's
  Findings, and, where the first linked theorem file is not the corrected theorem, `fix`, the
  linked file that is;
* the BibTeX entry of each page, which `references/<year>/*.md` carries itself (CONTRIBUTING.md,
  "The BibTeX entry of a page"). `appendix-errors.bib` here is generated from the entries of the
  pages with such a row, except those marked `**In the paper's bibliography.**`, whose key is the
  paper's own `references.bib` entry; the paper adds it to its `\bibliography`.

The run, and `--check`, fail when a `false`/`fixed` row has no description, a description
matches no such row, a `fix` is not a linked file, or a page with such a row has no well-formed entry. So a new `false`/`fixed` row needs its
description (and, for a new paper, its page's entry) in the same change. The paper needs `\usepackage{array,longtable,booktabs,hyperref}` (`longtable` after `arydshln`
if the paper loads it: the other order makes pdflatex loop at the end of the table),
`\input{appendix-errors}` where the table goes, and `appendix-errors` in `\bibliography{...}`;
the links point at `\coraleanrepo`, which the table `\providecommand`s as the repository's
`main` branch, so defining it first (`\newcommand{\coraleanrepo}{.../tree/<tag>/}`) pins them.

**The CORA bugs table** (`appendix-cora-bugs.tex`, label `tab:cora-bugs`) lists every CORA method
whose coverage row (`references/coverage/**/*.md`) has a `cora-issue —` note, the rule of
`scripts/check-references.py`. One `longtable` row each, sorted by group (contSet, contDynamics,
hybridDynamics, nn), then class, then method: the function as `\texttt{class/method}`, an asterisk
marking an *unsound* bug (CORA's result can miss reachable states, is not the enclosure it claims
to be, or is a wrong verdict a verification relies on; the others are too large, a wrong flag, a
crash or error path, or a documented behaviour that is not the code's), at most ten words on what
CORA gets wrong (the function name links to its page under `references/coverage/`), and links `[Cex]` to the Lean counterexample and `[Fix]` to the Lean file of the
corrected version (`---` where there is none). `python3 scripts/formalization-stats.py` writes it,
through `scripts/paper/cora-bugs-table.py`, which documents how the two files are picked. The data is
committed beside it, `experiments/paper/cora-bugs.json`: per coverage file and method, the
`description`, the `kind` (`unsound` or `other`), and optionally `cex` / `fix` (a linked file's
name, or `null` for none). The run, and `--check`,
fail when a `cora-issue` row has no entry, an entry matches no such row, or a `cex`/`fix` names a
file the row does not link. There is no bibliography; the paper needs the
same packages and the same `longtable`-after-`arydshln` order as for the errors table, and
`\input{appendix-cora-bugs}` where the table goes.

Not counted: which paper *results* also have a float refinement. Nothing in a row says so, float
files rarely cite the paper they refine, and matching `Real/` to `Float/` files by name finds
counterparts without a theorem and misses ones with one, so any number would be a guess. (For CORA
*methods* the coverage tables do say so: that is `float` against `proved`.)
