#!/usr/bin/env python3
"""The paper's appendix table of the errors found in the papers CORA cites.

Not run on its own: `scripts/formalization-stats.py` loads it, writes
`experiments/paper/latex/appendix-errors.tex` with the other generated files, and fails
(with or without `--check`) on any problem `table()` reports.

One row per `## Results` row of `references/<year>/*.md` classed `false` or `fixed`
(references/README.md, "The `Class` column"). The `false` rows come first, then a rule, then the
`fixed` ones; each group is sorted by year, then page, then the order of the rows in the page's
table. Four columns:

* the reference, `\\errorcite[<result>]{<key>}`, with the page's key from
  `experiments/paper/ledger-bibkeys.json`; a `false` row is marked with a dagger. The table
  `\\providecommand`s `\\errorcite` as `\\cite`; the paper defines it to cite into the
  appendix's own reference list unless the main text cites the paper too;
* a few words on what is wrong, from `experiments/paper/ledger-errors.json` (written by hand
  from the row's Class cell and the page's Findings; LaTeX-escaped here outside `$...$`);
* the Lean counterexample: the linked file that declares the first theorem the row names after
  `**Counterexample:**`, else the first linked file in a `Counterexamples/` folder or named `Not*`;
* the Lean fix, for a `fixed` row only: the `fix` of the row's description entry if it has one
  (a linked file's name), else the first linked file that is not a definition or operation
  (`Definitions/`, `Operations/`), not a counterexample file (as above, or declaring a named
  counterexample) and not named `Not*`. A `false` row has no fix.

A cell without a file is `---`. Links go to `\\coraleanrepo/<path>`, a macro the table
`\\providecommand`s as the repository's `main`, so the paper can point it at a tag.

Problems reported: a `false`/`fixed` row without a description, a description that matches no
such row, a `fix` that is not a linked file or is given for a `false` row, a page without a
BibTeX key, a key defined neither in `appendix-errors.bib` nor listed as one of the paper's own,
and a key in `appendix-errors.bib` no page uses.
"""

# Authors:       Tobias Ladner
# Written:       11-October-2026

import json
import re
from pathlib import Path, PurePosixPath

REPO_URL = "https://gitlab.lrz.de/cps/CORALean/-/blob/main"
CLASSES = ("false", "fixed")
CEX_NAME = re.compile(r"^Not(?=[A-Z])")
NOT_A_FIX = re.compile(r"Not(?=[A-Z])")
NOT_A_THEOREM_DIR = {"Definitions", "Operations"}


def is_cex(p):
    """A counterexample file: one in a `Counterexamples/` folder (#148), or named `Not*`."""
    return "Counterexamples" in p.parts or bool(CEX_NAME.search(p.stem))


def not_a_fix(p):
    """What is no repair: a counterexample file, or one named for a negation (`Not*`)."""
    return "Counterexamples" in p.parts or bool(NOT_A_FIX.search(p.stem))


def paths(cr):
    paper = cr.ROOT / "experiments" / "paper"
    return {
        "errors": paper / "ledger-errors.json",
        "keys": paper / "ledger-bibkeys.json",
        "bib": paper / "latex" / "appendix-errors.bib",
        "tex": paper / "latex" / "appendix-errors.tex",
    }


def ledger_rows(cr):
    """Every `false`/`fixed` row, in table order, as a dict."""
    out = []
    for path in sorted(cr.REFS.glob(cr.PAPER_GLOB)):
        text = path.read_text(encoding="utf-8")
        m = re.search(r"^## Results\s*$(.*?)(?=^## |\Z)", text, re.S | re.M)
        if not m:
            continue
        page = path.relative_to(cr.REFS).with_suffix("").as_posix()
        for cells in cr.rows_of(m.group(1)):
            if len(cells) != 4:
                continue
            klass = cr.CLASS.match(cells[3])
            if not klass or klass.group(1) not in CLASSES:
                continue
            where = cells[2]
            links = []
            for link in cr.LINK.findall(where):
                target = (path.parent / link).resolve()
                if link.endswith(".lean") and target.exists() and target not in links:
                    links.append(target)
            names = []
            for mm in cr.COUNTEREXAMPLE.finditer(where):
                names += [n.rsplit(".", 1)[-1] for n in re.findall(r"`([^`]+)`", mm.group(1))]
            out.append({"page": page, "label": cells[0].strip().strip("`").strip(),
                        "class": klass.group(1), "links": links, "cex_names": names})
    return out


def classify(cr, row):
    """`(counterexample file, files that are counterexamples)` of one row."""
    decls = {p: {n.rsplit(".", 1)[-1] for n, kind, _ in cr.lean_decls(p)
                 if kind in ("theorem", "lemma")} for p in row["links"]}
    cex_files = [p for p in row["links"] if any(n in decls[p] for n in row["cex_names"])]
    by_name = [p for p in row["links"] if is_cex(p)]
    first = None
    for n in row["cex_names"]:
        first = next((p for p in row["links"] if n in decls[p]), None)
        if first:
            break
    if first is None and by_name:
        first = by_name[0]
    return first, set(cex_files) | set(by_name)


def default_fix(row, cex_files):
    for p in row["links"]:
        if NOT_A_THEOREM_DIR & set(p.parts) or p in cex_files or not_a_fix(p):
            continue
        return p
    return None


def latex(s):
    """Escape LaTeX specials outside `$...$` (all but `~`, a tie); math passes through."""
    out = []
    for i, part in enumerate(re.split(r"(\$[^$]*\$)", s)):
        if i % 2:
            out.append(part)
            continue
        part = part.replace("\\", "\\textbackslash{}")
        part = re.sub(r"([&%#_{}])", r"\\\1", part)
        # `~` is left alone: a description writes `Prop.~2` with a tie on purpose
        part = part.replace("^", "\\textasciicircum{}")
        out.append(part)
    return "".join(out)


def cite_label(label):
    """`Prop. 32` -> `Prop.~32`: a tie after the kind of result."""
    return latex(re.sub(r"^(\S+)\s+", r"\1~", label, count=1))


def link(cr, path, text):
    if path is None:
        return "---"
    rel = PurePosixPath(path.relative_to(cr.ROOT).as_posix())
    return f"\\href{{\\coraleanrepo/{rel}}}{{[{text}]}}"


def table(cr):
    """`(text of appendix-errors.tex, [problems], counts)`."""
    p = paths(cr)
    problems = []
    descs = json.loads(p["errors"].read_text(encoding="utf-8"))
    keys = json.loads(p["keys"].read_text(encoding="utf-8"))
    bib = set(re.findall(r"^@\w+\{([^,\s]+),", p["bib"].read_text(encoding="utf-8"), re.M))
    paper_keys = set(keys.get("paper_keys", []))
    page_keys = keys.get("pages", {})
    rows = ledger_rows(cr)
    seen = set()
    body = {"false": [], "fixed": []}
    counts = {"false": 0, "fixed": 0, "cex": 0, "no_cex": [], "fix": 0, "no_fix": []}
    for row in rows:
        page, label = row["page"], row["label"]
        where = f"references/{page}.md: `{label}`"
        seen.add((page, label))
        entry = descs.get(page, {}).get(label)
        if entry is None:
            problems.append(f"{where} is `{row['class']}` and has no description in "
                            f"{p['errors'].relative_to(cr.ROOT).as_posix()}")
            entry = {}
        key = page_keys.get(page)
        if key is None:
            problems.append(f"references/{page}.md has a `{row['class']}` row and no BibTeX key in "
                            f"{p['keys'].relative_to(cr.ROOT).as_posix()}")
        cex, cex_files = classify(cr, row)
        fix = None
        if "fix" in entry:
            if row["class"] == "false":
                problems.append(f"{where} is `false`, so it has no fix, but its entry names one")
            else:
                fix = next((q for q in row["links"] if q.name == entry["fix"]), None)
                if fix is None:
                    problems.append(f"{where}: fix `{entry['fix']}` is not a Lean file the row links")
        elif row["class"] == "fixed":
            fix = default_fix(row, cex_files)
        counts[row["class"]] += 1
        if cex:
            counts["cex"] += 1
        else:
            counts["no_cex"].append(where)
        if row["class"] == "fixed":
            if fix:
                counts["fix"] += 1
            else:
                counts["no_fix"].append(where)
        mark = "\\textsuperscript{\\dag}" if row["class"] == "false" else ""
        ref = f"\\errorcite[{cite_label(label)}]{{{key or 'MISSING'}}}{mark}"
        body[row["class"]].append(f"{ref} & {latex(entry.get('description', ''))} & "
                                  f"{link(cr, cex, 'CEX')} & {link(cr, fix, 'FIX')} \\\\")
    for page, entries in descs.items():
        if page.startswith("_"):
            continue
        for label in entries:
            if (page, label) not in seen:
                problems.append(f"{p['errors'].relative_to(cr.ROOT).as_posix()}: `{page}` `{label}` "
                                "matches no `false`/`fixed` row")
    used = {page_keys[r["page"]] for r in rows if r["page"] in page_keys}
    for page, key in page_keys.items():
        if key not in bib and key not in paper_keys:
            problems.append(f"BibTeX key `{key}` of references/{page}.md is neither in "
                            f"{p['bib'].relative_to(cr.ROOT).as_posix()} nor a paper key")
        if not any(r["page"] == page for r in rows):
            problems.append(f"{p['keys'].relative_to(cr.ROOT).as_posix()}: references/{page}.md "
                            "has no `false`/`fixed` row")
    for key in sorted(bib - used):
        problems.append(f"{p['bib'].relative_to(cr.ROOT).as_posix()}: `{key}` is used by no page")
    papers = len({r["page"] for r in rows})
    text = f"""% Generated by scripts/formalization-stats.py from references/, experiments/paper/ledger-errors.json
% and experiments/paper/ledger-bibkeys.json; do not edit. Needs array, longtable, booktabs and hyperref; the
% keys are the paper's references.bib and appendix-errors.bib. Load longtable after arydshln, if any:
% the other order makes pdflatex loop at the table's end. Redefine \\coraleanrepo before the
% \\input to link a tag or a mirror.
\\providecommand{{\\coraleanrepo}}{{{REPO_URL}}}
\\providecommand{{\\errorcite}}[2][]{{\\cite[#1]{{#2}}}}% the paper may send these to a reference list of their own
\\begingroup
\\makeatletter\\let\\cite@adjust\\@empty\\makeatother % cite.sty: no space before the \\cite opening a row
\\footnotesize
\\setlength{{\\tabcolsep}}{{4pt}}
\\setlength{{\\LTcapwidth}}{{\\textwidth}}
\\begin{{longtable}}{{@{{}}>{{\\raggedright\\arraybackslash}}p{{3.0cm}}>{{\\raggedright\\arraybackslash}}p{{5.3cm}}cc@{{}}}}
\\caption{{List of incorrect statements in papers cited in CORA.}}
\\label{{tab:errors}}\\\\
\\toprule
Reference & Description & \\begin{{tabular}}[b]{{@{{}}c@{{}}}}Lean\\\\counterexample\\end{{tabular}} & \\begin{{tabular}}[b]{{@{{}}c@{{}}}}Lean\\\\fix\\end{{tabular}} \\\\
\\midrule
\\endfirsthead
\\toprule
Reference & Description & \\begin{{tabular}}[b]{{@{{}}c@{{}}}}Lean\\\\counterexample\\end{{tabular}} & \\begin{{tabular}}[b]{{@{{}}c@{{}}}}Lean\\\\fix\\end{{tabular}} \\\\
\\midrule
\\endhead
\\midrule
\\multicolumn{{4}}{{r}}{{\\textit{{continued on the next page}}}} \\\\
\\endfoot
\\bottomrule
\\endlastfoot
""" + "\n".join(body["false"] + (["\\midrule"] if body["false"] and body["fixed"] else [])
                + body["fixed"]) + """
\\end{longtable}
\\endgroup
"""
    return text, problems, counts
