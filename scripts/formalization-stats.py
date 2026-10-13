#!/usr/bin/env python3
"""How much of CORA is formalized, and where the papers were wrong.

    python3 scripts/formalization-stats.py            # JSON, figures and appendix
    python3 scripts/formalization-stats.py --check    # fail if any of them is stale

Reads `references/` through `scripts/check-references.py`'s own parser, so the
numbers are the tables' numbers and nothing is counted twice. Three counts:

1. the paper results (`references/<year>/`): per paper and in total, the rows in
   scope, formalized, and out of scope (by reason), and the formalized rows by
   `Class` (`correct`, `underspecified`, `proof-gap`, `fixed`, `false`), with every
   non-`correct` row and its reason listed. Each formalized row is also attributed
   to the CORA class of the first Lean file it links (see `bucket` in
   `check-references.py`), so the findings can be read per class;
2. CORA coverage (`references/coverage/`): per CORA class and in the groups the
   paper shows, the methods `proved`, `float` (by route a or b, see the README there), not yet, and out of scope (by
   reason), the float backlog (`needs_float`: `proved` with no float refinement
   yet) and the methods where CORA itself is wrong (`cora_issues`);
3. theorem categories: every public `theorem`/`lemma` under `src/CORALean`, in
   exactly one of paper theorems, float refinements, proof helpers and lemmas;
   `Examples/` theorems are counted apart.

Writes `experiments/paper/formalization-stats.json` and, under
`experiments/paper/latex/`,

* `figures/formalization/formalization.tikz`, the paper's overview figure in pgfplots, in the
  CORA colours of `cora-macs.sty`: (a) on the left, CORA methods per group (proved and runnable
  at float, proved and needing float, not yet; one thin rounded border round each bar, the
  out-of-scope count as "+n" after it), (b) and (c) stacked on the right: how the papers'
  results fared (and the in-scope ones not yet formalized), and what the Lean theorems are;
* `figures/formalization/formalization-caption.tex`, its caption, with the out-of-scope reasons
  and their counts;
* `figures/formalization/formalization-classes-sets.tikz`, `formalization-classes-contdynamics.tikz`,
  `formalization-classes-others.tikz` and `formalization-classes-specification.tikz`, the appendix's
  (a), split in four so each can float to its own page: one bar per CORA class in the same three
  segments, the set representations, the continuous dynamics, the hybrid-systems and neural-network
  groups under their headings, and the specification classes (`specification/`: specifications, STL,
  signals, analyzers; about as many classes as the set representations, so not appended to the
  short `others` figure);
* `figures/formalization/formalization-findings.tikz`, the appendix's (b): the formalized
  results per group, by segment (correct, proof gap, underspecified, fixed, false);
* `appendix-formalization.tex`, the appendix: the five figures above, each a figure of its own,
  and their captions;
* `figures/formalization/formalization.svg`, a dependency-free preview of the
  overview bars for a quick look without a TeX Live;
* `appendix-errors.tex`, the appendix table of every `false` and `fixed` result with its
  description, Lean counterexample and Lean fix (`scripts/errors-table.py`, which says where
  the descriptions and BibTeX keys come from); a row without a description, or a page without
  a key, fails the run and `--check`;
* `appendix-cora-bugs.tex`, the appendix table of the bugs found in CORA, one row per coverage
  row with a `cora-issue` note (`scripts/cora-bugs-table.py`); a row without an entry in
  `experiments/paper/cora-bugs.json`, or an entry without a row, fails the run and `--check`.

Everything is a function of `references/` and `src/`; no clock, no randomness, so
a rerun on unchanged tables rewrites identical files, and `check-references.py`
compares the JSON it finds with what `stats()` computes now.

Not reported: how many results also have a float refinement, as against how many
CORA *methods* do (that is `float` against `proved` above). Nothing in a paper
row says so, a float file rarely cites the paper it refines, and a name-based
match between `Real/` and `Float/` files finds counterparts that carry no theorem
and misses ones that do, so a count for the results would be a guess.
"""

# Authors:       Tobias Ladner
# Written:       01-October-2026

import importlib.util
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("check_references", HERE / "check-references.py")
cr = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cr)
spec = importlib.util.spec_from_file_location("errors_table", HERE / "errors-table.py")
et = importlib.util.module_from_spec(spec)
spec.loader.exec_module(et)
spec = importlib.util.spec_from_file_location("cora_bugs_table", HERE / "cora-bugs-table.py")
cb = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cb)

LATEX = cr.ROOT / "experiments" / "paper" / "latex"
FIG_DIR = LATEX / "figures" / "formalization"
APPENDIX = LATEX / "appendix-formalization.tex"
ERRORS = LATEX / "appendix-errors.tex"  # see scripts/errors-table.py
CORA_BUGS = LATEX / "appendix-cora-bugs.tex"  # see scripts/cora-bugs-table.py

# The colours of `experiments/paper/latex/cora-macs.sty`, as (name, rgb): the TikZ files name
# them, the SVG preview needs the numbers.
CORA = {
    "CORAcolorReachSet": (0.2706, 0.5882, 1.0000),
    "CORAcolorReachSet2": (0.6902, 0.8235, 1.0000),
    "CORAcolorSafe": (0.4706, 0.7725, 0.4980),
    "CORAcolorUnknown": (0.9290, 0.6940, 0.1250),
    "CORAcolorHighlight1": (1.0000, 0.6824, 0.2980),
    "CORAcolorUnsafe": (0.9451, 0.5529, 0.5686),
    "CORAcolorDarkRed": (0.6350, 0.0780, 0.1840),
    "CORAcolorBlue": (0.0000, 0.4470, 0.7410),
    "CORAcolorPurple": (0.4940, 0.1840, 0.5560),
    "white": (1.0, 1.0, 1.0),
}


def mix(a, b, pct):
    """`a!pct!b` of xcolor: `pct` percent of `a`, the rest `b`."""
    return tuple(round(pct / 100 * x + (1 - pct / 100) * y, 4) for x, y in zip(CORA[a], CORA[b]))


def blue_to_purple(i, n):
    """Step `i` of `n` (from 0) of the gradient `CORAcolorBlue` -> `CORAcolorPurple`: the TikZ
    colour expression and its rgb."""
    pct = round(100 * (1 - i / (n - 1)), 2)
    expr = {0: "CORAcolorBlue", n - 1: "CORAcolorPurple"}.get(i, f"CORAcolorBlue!{pct:g}!CORAcolorPurple")
    return (expr, mix("CORAcolorBlue", "CORAcolorPurple", pct))


# bar segments, left of the bar first. (key, label, TikZ colour, rgb). A bar has no
# per-segment outline, one thin rounded border round the whole bar.
def seg(key, label, name):
    return (key, label, name, CORA[name])


RESULT_CLASSES = [
    seg("correct", "correct", "CORAcolorSafe"),
    seg("proof-gap", "proof gap", "CORAcolorUnknown"),
    seg("underspecified", "underspecified", "CORAcolorHighlight1"),
    seg("fixed", "fixed", "CORAcolorUnsafe"),
    seg("false", "false", "CORAcolorDarkRed"),
]
# the bar of (b) is every result in scope: the formalized ones by how they fared, then the rest
RESULTS = RESULT_CLASSES + [seg("not_yet", "not yet", "white")]
COVERAGE = [
    seg("float", "proved, at float", "CORAcolorReachSet"),
    seg("proved", "proved, real only", "CORAcolorReachSet2"),
    seg("not_yet", "not yet", "white"),
]
THEOREMS = [
    ("paper", "paper theorems", *blue_to_purple(0, 4)),
    ("lemma", "lemmas", *blue_to_purple(1, 4)),
    ("float", "float refinements", *blue_to_purple(2, 4)),
    ("helper", "proof helpers", *blue_to_purple(3, 4)),
]
OUT_LEGEND = "+n: out of scope, not in the bar"
BAR = 6  # bar width in pt
OUTLINE = "0.2pt"  # the thin black outline of a bar and of a legend image
MIN_SEG = 0.04  # cm: the narrowest a non-empty segment is drawn, so that it stays visible

# what a bar is called; the groups are CORA's own directories. `LABEL` is the main
# figure's, `HEADING` the appendix's italic group headings.
LABEL = {"contSet": "Set representations", "contDynamics": "Cont. dynamics",
         "hybrid": "Hybrid systems", "neuralNetworks": "Neural networks",
         "specification": "Specification"}
HEADING = {"contSet": "Set representations (\\texttt{contSet})",
           "contDynamics": "Continuous dynamics (\\texttt{contDynamics})",
           "hybridDynamics": "Hybrid systems (\\texttt{hybridDynamics})",
           "nn": "Neural networks (\\texttt{nn})",
           "specification": "Specification (\\texttt{specification})"}
REASON_TEXT = {"plotting/display": "plotting and display", "random/sampling": "random sampling",
               "solver-dependent": "solver encodings",
               "io/conversion-to-matlab-objects": "conversions between MATLAB storage formats",
               "matlab-runtime": "MATLAB plumbing", "deprecated": "deprecated"}


def data_of(files_data):
    return files_data["cora_coverage"]


LINEWIDTH_CM = 12.2  # LNCS text width, to decide which segments are wide enough for a number
MONO = "\\ttfamily\\scriptsize"
CHAR_W = 0.13  # cm per character of MONO, for the text that must fit beside or in a bar
OUT_GREY = "black!40"


def luminance(rgb):
    r, g, b = rgb
    return 0.2126 * r + 0.7152 * g + 0.0722 * b


def panel(name, entries, segments, height, xlabel, legend, title=None, at=None, xmax=None,
          font=None, width=None, ylabels=True, out_legend=False, legend_columns=1, bar=BAR,
          title_at="at={(0.5,1)}", xtick=None, width_cm=4.0, bare=False, total=False, grid=True,
          framed=False):
    """One pgfplots axis of stacked horizontal bars.

    `entries` is `[(label, counts, out)]`: `counts` is `{key: n}`, or `None` for a heading
    row (a label and no bar), and `out` the number of out-of-scope methods written after the
    bar as `+n` (`None`: nothing). The segments have no outline; one thin black border with
    rounded corners runs round each whole bar, the fills clipped to it. A segment wide enough
    (`width_cm` is the axis width, for that decision) carries its value, in white on a dark segment. With `bare` the axis has no frame, ticks
    or x label (a single row of bars), and `total` writes the bar total after it. The labels
    are text, so the figure is legible without colour.
    """
    n = len(entries)
    out = []
    opts = [f"name={name}"]
    if at:
        opts.append(at)
    opts.append(f"height={height}")
    if width:
        opts.append(f"width={width}")
    if ylabels:
        opts += [f"ytick={{{','.join(str(i) for i in range(n))}}}",
                 "yticklabels={" + ",".join("{" + label + "}" for label, _, _ in entries) + "}"]
    else:
        opts += ["ytick=\\empty", "yticklabels={}"]
    opts += ["clip=false", "scaled ticks=false", "ytick style={draw=none}"]
    if bare:
        opts += ["axis line style={draw=none}", "xtick=\\empty", "xticklabels={}",
                 "tick style={draw=none}"]
    else:
        if xlabel:
            opts += [f"xlabel={{{xlabel}}}", "xlabel style={font=\\footnotesize}"]
        opts.append("tick label style={font=\\scriptsize}")
        # a framed axis is the paper's rounded box (cora-macs.sty), ticks along the bottom
        opts += ["rounded axis", "xtick pos=bottom"] if framed else ["axis lines*=left"]
        if grid:
            opts += ["xmajorgrids=true", "major x grid style={draw=black!15, line width=0.4pt}"]
    if font:
        opts.append(f"yticklabel style={{font={font}}}")
    if title:
        opts.append(f"title={{{title}}}")
        # as the paper's other figures: \\footnotesize, upright, centred over the plot
        opts.append(f"title style={{{title_at}, anchor=south, font=\\footnotesize}}")
    if xtick:
        opts.append(f"xtick={{{xtick}}}")
    if xmax:
        opts.append(f"xmax={xmax}")
    if legend:
        opts += [f"legend columns={legend_columns}, legend to name={legend}",
                 # framed as the legends of the paper's other figures, with rounded corners
                 "legend style={legend cell align=left, align=left, draw=white!15!black, "
                 "rounded corners, font=\\scriptsize, inner sep=1.5pt, "
                 "/tikz/every even column/.append style={column sep=0.5ex}, "
                 "/tikz/every odd column/.append style={column sep=0pt}}",
                 "legend image code/.code={\\draw[#1, draw=black, line width=" + OUTLINE + ", "
                 "rounded corners=1pt] (0cm,-0.6ex) rectangle (1.2ex,0.6ex);}"]
    out.append("\\begin{axis}[" + ",\n    ".join(opts) + "]")
    # the segments are filled by hand, clipped to the bar's rounded outline, so the fills meet
    # the outline exactly; the legend gets one image per segment instead of a plot
    out.append(f"\\addplot[draw=none, forget plot] coordinates {{(0,0) (0,{n - 1})}};")
    for key, label, color, _ in segments:
        if legend:
            out.append(f"\\addlegendimage{{fill={color}}}")
            out.append(f"\\addlegendentry{{{label}}}")
    if legend and out_legend:
        out.append("\\addlegendimage{empty legend}")
        out.append(f"\\addlegendentry{{{OUT_LEGEND}}}")
    half = bar / 2
    scale = width_cm / float(xmax)
    numbers = []  # the values, on a second axis over this one: the fills would cover nodes in it
    for i, (_, c, o) in enumerate(entries):
        if c is None:
            continue
        # every non-empty segment is drawn at least MIN_SEG wide, so a count of 1 or 2 stays
        # visible; the bar grows by what the small segments gain
        widths = {key: max(c.get(key, 0), MIN_SEG / scale) if c.get(key, 0) else 0
                  for key, *_ in segments}
        tot = sum(c.values())
        end = sum(widths.values())
        lo, hi = f"[yshift=-{half:g}pt]axis cs:", f"[yshift={half:g}pt]axis cs:"
        r = f"{min(1.5, bar / 4):g}pt"
        # the bar's outline: rounded corners, square on the left where it meets the y axis
        if not bare:
            shape = (f"({lo}0,{i}) [rounded corners={r}] -- ({lo}{end:g},{i}) -- ({hi}{end:g},{i}) "
                     f"[sharp corners] -- ({hi}0,{i}) -- cycle")
        else:
            shape = f"[rounded corners={r}] ({lo}0,{i}) rectangle ({hi}{end:g},{i})"
        if tot:
            out.append(f"\\begin{{scope}}\\clip{shape};")
        start = 0
        for key, _, color, rgb in segments:
            v, w = c.get(key, 0), widths[key]
            if v:
                out.append(f"\\fill[{color}] ({lo}{start:g},{i}) rectangle ({hi}{start + w:g},{i});")
            if v and (len(str(v)) * CHAR_W + 0.06) <= v * scale:
                col = "white" if luminance(rgb) < 0.6 else "black"
                numbers.append(f"\\node[font={MONO}, text={col}, inner sep=0pt] "
                               f"at (axis cs:{start + w / 2:g},{i}) {{{v}}};")
            start += w
        if tot:
            out.append("\\end{scope}")
            out.append(f"\\draw[black, line width={OUTLINE}] {shape};")
        text = (f"{tot}" if total else "") + (f"\\hspace{{{'0.8em' if total else '0em'}}}\\textcolor{{{OUT_GREY}}}{{+{o}}}" if o else "")
        if text:
            out.append(f"\\node[anchor=west, font={MONO}, inner sep=3pt] "
                       f"at (axis cs:{end:g},{i}) {{{text}}};")
    out.append("\\end{axis}")
    if numbers:
        over = [f"at={{({name}.south west)}}", "anchor=south west", f"height={height}",
                f"width={width}" if width else "", f"xmin=0, xmax={xmax}",
                "enlarge y limits={abs=0.7}", "hide axis", "clip=false"]
        out.append("\\begin{axis}[" + ", ".join(o for o in over if o) + "]")
        out.append(f"\\addplot[draw=none] coordinates {{(0,0) (0,{n - 1})}};")
        out.extend(numbers)
        out.append("\\end{axis}")
    return "\n".join(out)


def overview_entries(data):
    cov = data_of(data)
    groups = [(g, cov["groups"][g]) for g in cr.REPORT_GROUPS]
    methods = [(LABEL[g], {k: v[k] for k, *_ in COVERAGE}, v["out_of_scope"])
               for g, v in groups]
    th = cov["theorems"]
    theorems = [("Lean theorems", {k: th[k] for k, *_ in THEOREMS}, None)]
    t = data["totals"]
    results = [("Paper results", {**t["by_class"], "not_yet": t["not_formalized"]}, t["out_of_scope"])]
    return methods, theorems, results, groups


def tikz(data):
    """The overview figure: (a) on the left, (b) and (c) stacked on the right.

    It is sized in \\linewidth, so it fits the paper's column without a resize: (a) takes
    0.50 of it (its labels included) in the paper's rounded axis, the right column, from 0.59
    on, the rest (the "+n" included); (b) and (c) have no row labels, their
    titles name the bar.
    """
    methods, theorems, results, groups = overview_entries(data)
    mmax = max(sum(c.values()) for _, c, _ in methods)
    tmax = sum(theorems[0][1].values())
    rmax = sum(results[0][1].values())
    lab_a = 2.55  # width of the row labels of (a), in cm; (b) and (c) have none, their titles say it
    wa = 0.50 * LINEWIDTH_CM - lab_a
    # cm right of the bar of (b) for its "+n", and no more: the node's 3pt inner sep and the
    # text at CHAR_W per monospace character, so that bar and "+n" together fill the column.
    # The title and legend of (b) are centred on bar and tail together; (c) has no "+n", so
    # its bar fills the whole column.
    TAIL = 3 / 28.45 + CHAR_W * len(f"+{results[0][2]}") + 0.03
    xb = 0.59  # (b) and (c) start at this fraction of the line: a clear gap after (a)
    wb = (1 - xb) * LINEWIDTH_CM - TAIL  # what is left after the "+n"
    p_methods = panel("methods", methods, COVERAGE, "4.2cm", "", "coveragelegend",
                      title="(a) CORA functions",
                      at=f"at={{({lab_a}cm,0cm)}}, anchor=north west",
                      width=f"0.50\\linewidth-{lab_a}cm", width_cm=wa,
                      xmax="1000", bar=11, framed=True, legend_columns=3,
                      title_at=f"at={{(0.5,1)}}, xshift=-{lab_a / 2:g}cm, yshift=0.5ex",  # over axis and labels
                      xtick="0,200,400,600,800")
    # raised so that the title of (b), drawn 2mm into its axis, shares the baseline of (a)'s
    right = f"at={{({xb}\\linewidth,2mm+0.5ex)}}, anchor=north west"
    p_results = panel("results", results, RESULTS, "0.55cm", "", "resultlegend",
                      title="(b) Formalized paper statements", ylabels=False, at=right,
                      width=f"{wb:.2f}cm", width_cm=wb, xmax=f"{rmax}", legend_columns=3,
                      bar=11, bare=True, font="\\scriptsize",
                      title_at=f"at={{(0.5,1)}}, xshift={TAIL / 2:g}cm, yshift=-2mm")
    p_theorems = panel("theorems", theorems, THEOREMS, "0.55cm", "", "theoremlegend",
                       title="(c) Lean theorems", ylabels=False,
                       at="at={(results.south west)}, anchor=north west, yshift=-2.55cm",
                       width=f"{wb + TAIL:.2f}cm", width_cm=wb + TAIL, xmax=tmax,
                       legend_columns=2, bar=11, bare=True, font="\\scriptsize",
                       title_at="at={(0.5,1)}, yshift=-2mm")  # no "+n": the bar takes the tail too
    return f"""% Generated by scripts/formalization-stats.py from references/ and src/; do not edit.
% (a) CORA methods per group, on the left; (b) how the printed results of the papers fared, and
% (c) what the Lean theorems are, stacked on the right. One thin rounded border round each bar; a segment
% wide enough carries its value; the number "+n" after a bar counts the items out of scope, which
% are not in the bar. The figure is sized in
% \\linewidth and needs no \\resizebox.
\\begin{{tikzpicture}}
\\footnotesize
\\pgfplotsset{{every axis/.append style={{scale only axis,
    y dir=reverse, enlarge y limits={{abs=0.7}}, xmin=0}}}}

{p_methods}

{p_results}

{p_theorems}

\\node[anchor=north, inner sep=0pt] at ([xshift=-{lab_a / 2:g}cm, yshift=-0.6cm]methods.south) {{\\ref*{{coveragelegend}}}};
\\node[anchor=north, inner sep=0pt] at ([xshift={(wb + TAIL) / 2:.3f}cm, yshift=-0.2cm]results.south west) {{\\ref*{{resultlegend}}}};
\\node[anchor=north, inner sep=0pt] at ([yshift=-0.2cm]theorems.south) {{\\ref*{{theoremlegend}}}};
\\end{{tikzpicture}}
"""


def class_entries(data, groups=("contSet", "contDynamics", "hybridDynamics", "nn")):
    """Appendix (a): every CORA class, grouped under an italic heading per group."""
    cov = data_of(data)
    entries = []
    for g in groups:
        entries.append(("\\textit{" + HEADING[g] + "}", None, None))
        for e in cov["classes"]:
            if e["group"] == g:
                entries.append(("\\texttt{" + e["class"] + "}",
                                {k: e[k] for k, *_ in COVERAGE}, e["out_of_scope"]))
    return entries


def tikz_classes(data, groups=("contSet", "contDynamics", "hybridDynamics", "nn")):
    entries = class_entries(data, groups)
    n = len(entries)
    xmax = max(sum(c.values()) for _, c, _ in entries if c is not None)
    body = panel("classes", entries, COVERAGE, f"{0.3 * n:.2f}cm",
                 "", "classlegend", width="0.5\\linewidth",
                 width_cm=0.5 * LINEWIDTH_CM, xmax=f"{1.12 * xmax:.0f}", font="\\scriptsize",
                 legend_columns=3, bar=5, framed=True)
    return f"""% Generated by scripts/formalization-stats.py from references/coverage/; do not edit.
% CORA methods per class, grouped by CORA's directories; one thin rounded border round each bar; the
% number "+n" after a bar counts the methods out of scope, which are not in the bar.
\\begin{{tikzpicture}}
\\footnotesize
\\pgfplotsset{{every axis/.append style={{scale only axis,
    y dir=reverse, enlarge y limits={{abs=0.7}}, xmin=0}}}}

{body}

\\node[anchor=north, yshift=-1ex] at (current bounding box.south) {{\\ref*{{classlegend}}}};
\\end{{tikzpicture}}
"""


def findings_entries(data):
    """Appendix (b): the formalized results of the papers, per group of CORA classes, by how
    they fared (correct included)."""
    cov = data_of(data)
    keys = [k for k, *_ in RESULT_CLASSES]
    entries = [(LABEL[g], {k: cov["groups"][g]["findings"][k] for k in keys}, None)
               for g in cr.REPORT_GROUPS]
    off = {k: sum(f[k] for f in cov["findings_not_on_a_class"].values()) for k in keys}
    entries.append(("Other", off, None))
    return entries


def tikz_findings(data):
    entries = findings_entries(data)
    xmax = max(sum(c.values()) for _, c, _ in entries)
    xmax = f"{1.06 * xmax:.0f}"  # headroom: the longest bar stays clear of the rounded frame
    body = panel("findings", entries, RESULT_CLASSES, f"{0.55 * len(entries) + 0.4:.2f}cm",
                 "", "findinglegend",
                 width="0.6\\linewidth", width_cm=0.6 * LINEWIDTH_CM, xmax=xmax, legend_columns=5, bar=8,
                 framed=True)
    return f"""% Generated by scripts/formalization-stats.py from references/; do not edit.
% The formalized results of the papers per group of CORA classes, by how they fared, by the
% first Lean file a result links.
\\begin{{tikzpicture}}
\\footnotesize
\\pgfplotsset{{every axis/.append style={{scale only axis,
    y dir=reverse, enlarge y limits={{abs=0.7}}, xmin=0}}}}

{body}

\\node[anchor=north, yshift=-1ex] at (current bounding box.south) {{\\ref*{{findinglegend}}}};
\\end{{tikzpicture}}
"""


def reasons(data):
    r = data_of(data)["totals"]["out_of_scope_by_reason"]
    items = sorted(((n, k) for k, n in r.items() if n), reverse=True)
    return ", ".join(f"{REASON_TEXT[k]} ({n})" for n, k in items)


def result_reasons(data):
    r = data["totals"]["out_of_scope_by_reason"]
    return ", ".join(f"{k.replace('-', ' ')} ({n})"
                     for n, k in sorted(((n, k) for k, n in r.items() if n), reverse=True))


def caption(data):
    """The overview figure's caption: short; the reasons for "out of scope" are the appendix's."""
    return """% Generated by scripts/formalization-stats.py from references/ and src/; do not edit.
Formalization status of CORALean: (a)~formalized CORA functions, (b)~formalized statements of papers, (c)~Lean theorems by kind; \\emph{+n} counts out-of-scope items.
"""


def appendix(data):
    cov_out = data_of(data)["totals"]["out_of_scope"]
    res_out = data["totals"]["out_of_scope"]
    text = """% Generated by scripts/formalization-stats.py from references/; do not edit.
% The appendix of the paper's formalization section: coverage and findings per CORA class.
\\section{CORA coverage and findings per class}
\\label{app:formalization}

Figs.~\\ref{fig:formalization-classes-sets}, \\ref{fig:formalization-classes-contdynamics},
\\ref{fig:formalization-classes-others} and \\ref{fig:formalization-classes-specification} show the
CORA methods per class and
Fig.~\\ref{fig:formalization-findings} the formalized results of the papers per group, by how they fared.
Not in the bars are @COV@ CORA methods that are out of scope, by reason @REASONS@, and @RES@ results
of the papers, by reason @RESREASONS@.

\\begin{figure}[tp]
    \\centering
    \\includetikz{./figures/formalization/formalization-classes-sets}
    \\caption{CORA methods per set representation; \\emph{+n} counts out-of-scope methods.}
    \\label{fig:formalization-classes-sets}
\\end{figure}

\\begin{figure}[tp]
    \\centering
    \\includetikz{./figures/formalization/formalization-classes-contdynamics}
    \\caption{CORA methods per class of continuous dynamics; \\emph{+n} counts out-of-scope methods.}
    \\label{fig:formalization-classes-contdynamics}
\\end{figure}

\\begin{figure}[tp]
    \\centering
    \\includetikz{./figures/formalization/formalization-classes-others}
    \\caption{CORA methods per class of hybrid systems and neural networks; \\emph{+n} counts
    out-of-scope methods.}
    \\label{fig:formalization-classes-others}
\\end{figure}

\\begin{figure}[tp]
    \\centering
    \\includetikz{./figures/formalization/formalization-classes-specification}
    \\caption{CORA methods per class of specifications (specification objects, signal temporal logic,
    signals and analyzers); \\emph{+n} counts out-of-scope methods.}
    \\label{fig:formalization-classes-specification}
\\end{figure}

\\begin{figure}[t]
    \\centering
    \\includetikz{./figures/formalization/formalization-findings}
    \\caption{Formalized paper results per group of CORA classes.}
    \\label{fig:formalization-findings}
\\end{figure}
"""
    return (text.replace("@COV@", str(cov_out)).replace("@REASONS@", reasons(data))
            .replace("@RES@", str(res_out)).replace("@RESREASONS@", result_reasons(data)))



def svg(data):
    methods, theorems, results, _ = overview_entries(data)
    panels = [("(a) CORA functions", methods, COVERAGE),
              ("(b) Formalized paper statements", results, RESULTS), ("(c) Lean theorems", theorems, THEOREMS)]
    left, width, row_h = 150, 520, 20
    h = 30 + sum(row_h * len(es) + 60 for _, es, _ in panels)
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{left + width + 80}" height="{h}" '
           'font-family="sans-serif" font-size="11">',
           '<rect width="100%" height="100%" fill="white"/>']
    y = 20
    for title, entries, segs in panels:
        out.append(f'<text x="{left}" y="{y}" font-weight="bold">{title}</text>')
        y += 8
        scale = width / max(sum(c.values()) for _, c, _ in entries)
        for label, counts, oos in entries:
            out.append(f'<text x="{left - 8}" y="{y + 11}" text-anchor="end">{label}</text>')
            x = left
            for key, _, _, color in segs:
                v = counts.get(key, 0)
                if v:
                    col = "rgb(%d,%d,%d)" % tuple(round(255 * c) for c in color)
                    out.append(f'<rect x="{x:.1f}" y="{y}" width="{v * scale:.1f}" height="14" '
                               f'fill="{col}"/>')
                    if v * scale > 22:
                        txt = "#fff" if sum(color) < 1.2 else "#000"
                        out.append(f'<text x="{x + v * scale / 2:.1f}" y="{y + 11}" '
                                   f'text-anchor="middle" font-size="9" fill="{txt}">{v}</text>')
                x += v * scale
            out.append(f'<rect x="{left}" y="{y}" width="{x - left:.1f}" height="14" fill="none" '
                       'stroke="#000" stroke-width="0.8"/>')
            if oos:
                out.append(f'<text x="{x + 5:.1f}" y="{y + 11}" font-size="9" '
                           f'fill="#888">+{oos}</text>')
            y += row_h
        for j, (_, label, _, color) in enumerate(segs):
            col = "rgb(%d,%d,%d)" % tuple(round(255 * c) for c in color)
            lx, yy = left + (j % 3) * 190, y + 6 + (j // 3) * 16
            out.append(f'<rect x="{lx}" y="{yy}" width="12" height="12" fill="{col}" '
                       'stroke="#000" stroke-width="0.8"/>')
            out.append(f'<text x="{lx + 18}" y="{yy + 10}">{label}</text>')
        if segs is COVERAGE:
            out.append(f'<text x="{left}" y="{y + 40}" font-size="10" fill="#888">'
                       f'{OUT_LEGEND}</text>')
        y += 52
    out.append("</svg>")
    return "\n".join(out) + "\n"


def outputs():
    papers = [cr.Paper(p, lambda m: None) for p in sorted(cr.REFS.glob(cr.PAPER_GLOB))]
    data = cr.stats(papers)
    errors, problems, _ = et.table(cr)
    bugs, bug_problems, _ = cb.table(cr)
    problems = [f"appendix-errors.tex: {m}" for m in problems] + \
               [f"appendix-cora-bugs.tex: {m}" for m in bug_problems]
    return {
        cr.STATS_JSON: json.dumps(data, indent=2, ensure_ascii=False) + "\n",
        FIG_DIR / "formalization.tikz": tikz(data),
        FIG_DIR / "formalization-classes-sets.tikz": tikz_classes(data, ("contSet",)),
        FIG_DIR / "formalization-classes-contdynamics.tikz": tikz_classes(data, ("contDynamics",)),
        FIG_DIR / "formalization-classes-others.tikz": tikz_classes(data, ("hybridDynamics", "nn")),
        FIG_DIR / "formalization-classes-specification.tikz": tikz_classes(data, ("specification",)),
        FIG_DIR / "formalization-findings.tikz": tikz_findings(data),
        FIG_DIR / "formalization-caption.tex": caption(data),
        FIG_DIR / "formalization.svg": svg(data),
        APPENDIX: appendix(data),
        ERRORS: errors,
        CORA_BUGS: bugs,
    }, data, problems


def main():
    files, data, problems = outputs()
    for problem in problems:
        print(problem)
    if "--check" in sys.argv[1:]:
        stale = [p for p, text in files.items()
                 if not p.exists() or p.read_text(encoding="utf-8") != text]
        for p in stale:
            print(f"{p.relative_to(cr.ROOT).as_posix()}: stale — rerun scripts/formalization-stats.py")
        return 1 if stale or problems else 0
    for p, text in files.items():
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
        print(f"wrote {p.relative_to(cr.ROOT).as_posix()}")
    t = data["totals"]
    print(f"{t['formalized']}/{t['in_scope']} paper results formalized; " +
          ", ".join(f"{k} {v}" for k, v in t["by_class"].items()))
    c = data["cora_coverage"]["totals"]
    print(f"{c['methods']} CORA methods: {c['float']} float, {c['proved']} proved (float backlog), "
          f"{c['not_yet']} not yet, {c['out_of_scope']} out of scope")
    th = data["cora_coverage"]["theorems"]
    print("theorems: " + ", ".join(f"{k} {v}" for k, v in th.items()))
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
