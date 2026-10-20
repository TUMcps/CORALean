#!/usr/bin/env python3
"""The paper's appendix table of the bugs found in CORA.

Not run on its own: `scripts/formalization-stats.py` loads it, writes
`experiments/paper/latex/appendix-cora-bugs.tex` with the other generated files, and fails
(with or without `--check`) on any problem `table()` reports.

One row per coverage row of `references/coverage/**/*.md` whose note has a `cora-issue —` part
(the rule of `scripts/check-references.py`, `CORA_ISSUE`), sorted by group (`CORA_GROUPS`), then
class, then method. Four columns:

* the CORA function, `\\texttt{<class>/<method>}`, from the coverage file and the row's method
  cell, linked to that coverage page; a row whose result is unsound is marked with an asterisk;
* a few words on what CORA gets wrong, from `experiments/paper/cora-bugs.json` (written by hand
  from the row's `cora-issue —` text; LaTeX-escaped here outside `$...$`), with the `kind` of the bug: `unsound` (the result can miss reachable states, is not
  the enclosure it claims to be, or is a wrong verdict a verification relies on) or `other` (too
  large, a wrong flag, a crash or error path, a documented behaviour that is not the code's);
* the Lean counterexample: the entry's `cex` if it has one (`null`: none), else the first linked file in a `Counterexamples/` folder or named
  `*Not{Inner,Outer,Sound,Mem}*`, else the first that declares a theorem
  named `*counterexample*`;
* the Lean fix: the entry's `fix` if it has one (`null`: none), else the first file the row's third column
  links that is not a counterexample and does not transcribe CORA (`Cora` in its name); a row
  whose state is `—` has none.

The files a row links are those of its third column and of its note (the note carries the full
text of what CORA gets wrong and the Lean files that witness it). A `cex` or `fix` override is a file's name (or its path when two linked files share
the name) and must be one of them. A cell without a file is `---`. Links go to
`\\coraleanrepo/<path>`, a macro the table `\\providecommand`s as the repository's `main`.

Problems reported: a `cora-issue` row without an entry, an entry that matches no such row, a
`kind` that is neither `unsound` nor `other`, a description over ten words, a `cex`/`fix` that is
not a linked file, a `fix` on a row whose state is `—`.
"""

# Authors:       Tobias Ladner
# Written:       12-October-2026

import json
import re
from pathlib import Path, PurePosixPath

REPO_URL = "https://gitlab.lrz.de/cps/CORALean/-/blob/main"
CEX_NAME = re.compile(r"Not(?:Inner|Outer|Sound|Mem)")


def is_cex(p):
    """A counterexample file: one in a `Counterexamples/` folder (#148), or named `*Not{Inner,...}*`."""
    return "Counterexamples" in p.parts or bool(CEX_NAME.search(p.stem))
DECL_CEX = re.compile(r"counterexample", re.I)
KINDS = ("unsound", "other")
MAX_WORDS = 10


def json_path(cr):
    return cr.ROOT / "experiments" / "paper" / "cora-bugs.json"


def coverage_rows(cr):
    """Every `cora-issue` row, in table order, as a dict."""
    out = []
    for group in cr.CORA_GROUPS:
        for path in sorted((cr.COVERAGE / group).glob("*.md")):
            for cells in cr.rows_of(path.read_text(encoding="utf-8")):
                if len(cells) != 4 or cells[0] == "Method":
                    continue
                method, state, where, note = cells
                if not cr.CORA_ISSUE.search(note):
                    continue
                links = []
                for link in cr.LINK.findall(where) + cr.LINK.findall(note):
                    target = (path.parent / link).resolve()
                    if link.endswith(".lean") and target.exists() and target not in links:
                        links.append(target)
                out.append({"group": group, "cls": path.stem, "method": method.strip("`"),
                            "state": state, "links": links,
                            "col3": [t for t in links if t in
                                     {(path.parent / l).resolve() for l in cr.LINK.findall(where)}]})
    return out


def find_file(cr, name, files):
    """The linked file an override names: a bare file name (the first so named), or a repository path."""
    hits = [p for p in files if p.name == name or p.relative_to(cr.ROOT).as_posix() == name]
    return hits[0] if hits else None


def latex(s):
    """Escape LaTeX specials outside `$...$`; math passes through."""
    out = []
    for i, part in enumerate(re.split(r"(\$[^$]*\$)", s)):
        if i % 2:
            out.append(part)
            continue
        part = part.replace("\\", "\\textbackslash{}")
        part = re.sub(r"([&%#_{}])", r"\\\1", part)
        part = part.replace("^", "\\textasciicircum{}")
        # pdflatex cannot typeset a character outside ASCII in text (`ℝⁿ` broke the paper
        # once): write it as math, `$\\mathbb{R}^n$`, which passes through above.
        bad = sorted({c for c in part if ord(c) > 127})
        if bad:
            raise SystemExit(f"cora-bugs-table: non-ASCII {''.join(bad)!r} outside $...$ in {s!r}; "
                             "write it as LaTeX math")
        out.append(part)
    return "".join(out)


def link(cr, path, text):
    if path is None:
        return "---"
    rel = PurePosixPath(path.relative_to(cr.ROOT).as_posix())
    return f"\\href{{\\coraleanrepo/{rel}}}{{[{text}]}}"


def table(cr):
    """`(text of appendix-cora-bugs.tex, [problems], counts)`."""
    jp = json_path(cr)
    jrel = jp.relative_to(cr.ROOT).as_posix()
    problems = []
    data = json.loads(jp.read_text(encoding="utf-8"))
    rows = coverage_rows(cr)
    seen = set()
    body = []
    counts = {"rows": 0, "unsound": 0, "other": 0, "cex": 0, "fix": 0, "no_cex": [], "no_fix": []}
    for row in rows:
        key = f"{row['group']}/{row['cls']}"
        where = f"references/coverage/{key}.md: `{row['method']}`"
        seen.add((key, row["method"]))
        entry = data.get(key, {}).get(row["method"])
        if entry is None:
            problems.append(f"{where} has a `cora-issue` note and no entry in {jrel}")
            entry = {}
        if "findings" in entry:
            problems.append(f"{where}: `findings` is obsolete; the row's note carries the text and the links")
        files = list(row["links"])
        kind = entry.get("kind")
        if kind not in KINDS:
            problems.append(f"{where}: `kind` is `{kind}`, not one of {', '.join(KINDS)}")
        desc = entry.get("description", "")
        if len(re.sub(r"\$[^$]*\$", "X", desc).split()) > MAX_WORDS:
            problems.append(f"{where}: description is over {MAX_WORDS} words")
        if "cex" in entry and entry["cex"] is None:
            cex = None
        elif "cex" in entry:
            cex = find_file(cr, entry["cex"], files)
            if cex is None:
                problems.append(f"{where}: cex `{entry['cex']}` is not a Lean file the row links")
        else:
            cex = next((p for p in files if is_cex(p)), None)
            if cex is None:
                cex = next((p for p in files if any(
                    k in ("theorem", "lemma") and DECL_CEX.search(n)
                    for n, k, _ in cr.lean_decls(p))), None)
        fix = None
        if "fix" in entry and entry["fix"] is None:
            pass
        elif "fix" in entry:
            fix = find_file(cr, entry["fix"], files)
            if fix is None:
                problems.append(f"{where}: fix `{entry['fix']}` is not a Lean file the row links")
            elif row["state"] == "—":
                problems.append(f"{where}: state is `—`, so there is no fix, but its entry names one")
        elif row["state"] != "—":
            fix = next((p for p in row["col3"]
                        if not is_cex(p) and "Cora" not in p.stem
                        and "CORA" not in p.stem), None)
            if fix is None:
                problems.append(f"{where}: no default fix; name one under `fix` (null for none)")
        counts["rows"] += 1
        if kind in KINDS:
            counts[kind] += 1
        if cex:
            counts["cex"] += 1
        else:
            counts["no_cex"].append(where)
        if fix:
            counts["fix"] += 1
        else:
            counts["no_fix"].append(where)
        mark = "\\textsuperscript{*}" if kind == "unsound" else ""
        # a break point after the slash and each underscore, so a long name does not overfull
        name = latex(f"{row['cls']}/{row['method']}").replace("/", "/\\allowbreak{}").replace("\\_", "\\_\\allowbreak{}")
        page = f"\\coraleanrepo/references/coverage/{key}.md"
        body.append(f"\\href{{{page}}}{{\\texttt{{{name}}}}}{mark} & {latex(desc)} & "
                    f"{link(cr, cex, 'Cex')} & {link(cr, fix, 'Fix')} \\\\")
    order = {g: i for i, g in enumerate(cr.CORA_GROUPS)}
    keyed = sorted(zip(rows, body), key=lambda rb: (order[rb[0]["group"]], rb[0]["cls"].lower(),
                                                    rb[0]["method"].lower()))
    body = [b for _, b in keyed]
    for key, entries in data.items():
        if key.startswith("_"):
            continue
        for method in entries:
            if (key, method) not in seen:
                problems.append(f"{jrel}: `{key}` `{method}` matches no `cora-issue` row")
    n = len(rows)
    text = f"""% Generated by scripts/formalization-stats.py from references/coverage/ and experiments/paper/cora-bugs.json;
% do not edit. Needs array, longtable, booktabs and hyperref; no bibliography. Load longtable
% after arydshln, if any: the other order makes pdflatex loop at the table's end. Redefine
% \\coraleanrepo before the \\input to link a tag or a mirror.
\\providecommand{{\\coraleanrepo}}{{{REPO_URL}}}
\\begingroup
\\footnotesize
\\setlength{{\\tabcolsep}}{{4pt}}
\\setlength{{\\LTcapwidth}}{{\\textwidth}}
\\begin{{longtable}}{{@{{}}>{{\\raggedright\\arraybackslash}}p{{3.9cm}}>{{\\raggedright\\arraybackslash}}p{{4.4cm}}cc@{{}}}}
\\caption{{List of bugs found in CORA while formalizing it in Lean 4.}}
\\label{{tab:cora-bugs}}\\\\
\\toprule
CORA function & Description & \\begin{{tabular}}[b]{{@{{}}c@{{}}}}Lean\\\\counterexample\\end{{tabular}} & \\begin{{tabular}}[b]{{@{{}}c@{{}}}}Lean\\\\fix\\end{{tabular}} \\\\
\\midrule
\\endfirsthead
\\toprule
CORA function & Description & \\begin{{tabular}}[b]{{@{{}}c@{{}}}}Lean\\\\counterexample\\end{{tabular}} & \\begin{{tabular}}[b]{{@{{}}c@{{}}}}Lean\\\\fix\\end{{tabular}} \\\\
\\midrule
\\endhead
\\midrule
\\multicolumn{{4}}{{r}}{{\\textit{{continued on the next page}}}} \\\\
\\endfoot
\\bottomrule
\\endlastfoot
""" + "\n".join(body) + """
\\end{longtable}
\\endgroup
"""
    return text, problems, counts
