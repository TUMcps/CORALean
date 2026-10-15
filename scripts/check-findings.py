#!/usr/bin/env python3
"""Check the findings about CORA, which live in the coverage tables.

A bug in CORA is a `cora-issue —` part of the note of its row in
`references/coverage/<group>/<class>.md`, and an entry of `experiments/paper/cora-bugs.json`.
A departure from CORA that belongs to no single method is a row of the table in the section
"Departures from CORA that belong to no single method" of `references/coverage/README.md`.
Checked:

* the departures table: three cells a row, no two rows with one subject, a non-empty
  "What differs", and every link resolves to an existing path (anchors are not checked; a
  details cell of `—` is allowed: nothing is formalized and the row is the whole argument);
* every `cora-issue —` part (from the marker to the next marker or the end of the note): every
  relative link in it resolves, and it has its Lean witness or says why not. It has the witness
  when it links a Lean file; or the row links a Lean file in a `Counterexamples/` folder; or
  it speaks of a counterexample or witness and the row links a Lean file (a theorem of the third
  column). It says why not by "no Lean witness", "no Lean link", "not statable", "outside the
  model", "MATLAB error", "cannot run", "no CORA claim refuted" or "Not formalized:";
* every entry of `cora-bugs.json` names a coverage file and a row of it, and that row has a
  `cora-issue —` part; every such row has an entry; an entry has no `findings` field.

Usage: `python3 scripts/check-findings.py [--root DIR]`. Exit 1 on a defect.
"""
import argparse
import json
import re
import sys
from pathlib import Path

SECTION = "## Departures from CORA that belong to no single method"
ISSUE = re.compile(r"(?:^|[;.]\s+)cora-issue\s+—")   # the rule of check-references.py (CORA_ISSUE)
LINK = re.compile(r"\[(?:[^\[\]]|\[[^\]]*\])*\]\(([^)\s]+)\)")
CELL = re.compile(r"(?<!\\)\|")
NO_WITNESS = re.compile(
    r"no Lean (?:witness|link|counterexample)|not statable|outside the model|MATLAB error|"
    r"cannot run|cannot be stated|no CORA claim refuted|Not formalized[:;.]", re.I)
GROUPS = ("contSet", "contDynamics", "hybridDynamics", "nn", "specification", "others")


def cells_of(line):
    return [c.strip() for c in CELL.split(line.strip()[1:-1])]


def relative_links(text):
    return [t for t in LINK.findall(text) if not re.match(r"[a-z]+:", t) and not t.startswith("#")]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=str(Path(__file__).resolve().parent.parent))
    root = Path(ap.parse_args().root).resolve()
    cov = root / "references" / "coverage"
    errors = []

    # --- the departures table ------------------------------------------------------------
    readme = cov / "README.md"
    text = readme.read_text(encoding="utf-8")
    if SECTION not in text:
        errors.append(f"{readme.relative_to(root)}: no section {SECTION!r}")
        body = ""
    else:
        i = text.index(SECTION)
        j = text.find("\n## ", i + 3)
        body = text[i:len(text) if j < 0 else j]
    subjects = {}
    n_dep = 0
    for no, line in enumerate(body.splitlines(), 1):
        if not line.startswith("| ") or line.startswith("|---") or line.startswith("| Subject"):
            continue
        n_dep += 1
        # a row's subject is its first cell, its details the last; the middle may hold a bare `|`
        body_cells = line[2:].rstrip()[:-1]
        subject, rest = body_cells.split(" | ", 1)
        what, _, details = rest.rpartition("|")
        subject = re.sub(r"\s+", " ", subject.strip())
        if subject in subjects:
            errors.append(f"coverage/README.md: duplicate departure {subject!r}")
        subjects[subject] = no
        if not what.strip():
            errors.append(f"coverage/README.md: departure {subject!r} says nothing in 'What differs'")
        for target in relative_links(line):
            if not (readme.parent / target.partition("#")[0]).exists():
                errors.append(f"coverage/README.md: departure {subject!r}: link {target!r} does not resolve")

    # --- the cora-issue parts ---------------------------------------------------------------
    rows = {}   # (group/class, method) -> number of cora-issue parts
    for group in GROUPS:
        for path in sorted((cov / group).glob("*.md")):
            key = f"{group}/{path.stem}"
            for line in path.read_text(encoding="utf-8").splitlines():
                if not line.startswith("| "):
                    continue
                cells = cells_of(line)
                if len(cells) != 4 or cells[0] == "Method":
                    continue
                method, where, note = cells[0].strip("`"), cells[2], cells[3]
                marks = [m.start() for m in ISSUE.finditer(note)]
                if not marks:
                    continue
                rows[(key, method)] = len(marks)
                lean_in_row = [t for t in relative_links(where + " " + note) if t.endswith(".lean")]
                cex_in_row = [t for t in lean_in_row if "/Counterexamples/" in "/" + t]
                for k, a in enumerate(marks):
                    b = marks[k + 1] if k + 1 < len(marks) else len(note)
                    part = note[a:b]
                    tag = f"{key}.md: `{method}`" + (f" (part {k + 1})" if len(marks) > 1 else "")
                    for target in relative_links(part):
                        if not (path.parent / target.partition("#")[0]).exists():
                            errors.append(f"{tag}: link {target!r} does not resolve")
                    has_link = any(t.endswith(".lean") for t in relative_links(part))
                    speaks = re.search(r"counterexample|witness", part, re.I) and lean_in_row
                    if not (has_link or cex_in_row or speaks or NO_WITNESS.search(part)):
                        errors.append(f"{tag}: the `cora-issue` note has no Lean witness link and does not "
                                      "say why there is none")

    # --- cora-bugs.json --------------------------------------------------------------------
    data = json.loads((root / "experiments" / "paper" / "cora-bugs.json").read_text(encoding="utf-8"))
    entries = set()
    for key, d in data.items():
        if key.startswith("_"):
            continue
        for method, entry in d.items():
            entries.add((key, method))
            if not (cov / f"{key}.md").exists():
                errors.append(f"cora-bugs.json: `{key}` is no coverage file")
            elif (key, method) not in rows:
                errors.append(f"cora-bugs.json: `{key}` `{method}` has no coverage row with a "
                              "`cora-issue —` part")
            if "findings" in entry:
                errors.append(f"cora-bugs.json: `{key}` `{method}`: `findings` is obsolete")
    for key, method in sorted(set(rows) - entries):
        errors.append(f"{key}.md: `{method}` has a `cora-issue —` part and no entry in cora-bugs.json")

    for e in errors:
        print(e)
    if errors:
        sys.exit(1)
    print(f"check-findings: {n_dep} departures (no duplicate subjects, links resolve), "
          f"{sum(rows.values())} cora-issue parts on {len(rows)} rows, {len(entries)} cora-bugs.json entries, "
          "all consistent")


if __name__ == "__main__":
    main()
