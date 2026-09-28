# Paper figures and tables

Renders the evaluation floats of the paper (Fig. 4-5, Tab. 1-3) from the generated results,
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
collected `figures/evaluation/` tree, at `results/paper-v9`), it also
`diff -r`s it against the freshly collected tree and fails on any
difference. See `experiments/README.md`'s "`experiments/paper/make_paper.sh`"
section for the full command sequence from a results directory to
`paper_floats.pdf`.
