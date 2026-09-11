#!/usr/bin/env python3
"""Checks `references/` against the tree, so a coverage table cannot rot.

    python3 scripts/check-references.py

`references/` holds one file per publication, listing that paper's numbered
results and, for each, where it is formalized. Nothing here reads Lean: the
cites are in module docstrings, which `check-conventions.sh` already keeps
well-formed. What this adds is that the two agree — every paper cited has a
file, every link resolves and points at a file that really cites that result,
every result cited somewhere is a row, and the README's counts are the counts.

Exit status is 1 on any complaint, so it belongs in CI beside the conventions.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
REFS = ROOT / "references"

# A `## References` entry, `* [1] ...`, continued by any indented line under it.
ENTRY = re.compile(r"^\s*\*\s*\[(\d+)\]\s*(.*)$")
# A cite, `[1]` or `[1, Prop. 3.3]`. The locator is kept only when it looks like
# one: `[0, r]` is an interval and `[1, 2]` a pair of cites, neither a result.
CITE = re.compile(r"\[(\d+)((?:,\s*)[^\]\n]*)?\]")
LOCATOR = re.compile(
    r"^(Thm\.|Prop\.|Lemma|Def\.|Cor\.|Sec\.|Eq\.|Alg\.|Ch\.|Table|Fig\.|Remark|"
    r"Heuristic|Assumption|§|pp?\.)", re.I
)
LINK = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
# A README row: the paper cell links the file, the last cell is the count —
# formalized over in scope, then how many rows sit outside the count entirely.
STATUS = re.compile(r"^(🟢|🟡|🔴|⚪)\s*(\d+)/(\d+)\s*\|\s*(\d+)$")

FLAT = lambda s: re.sub(r"\s+", " ", s).strip()


def locator(s):
    """One spelling per result, so `§3.3.1` and `Sec. 3.3.1` are one row.

    Parentheses around an equation number are the paper's, not a distinction —
    `Eq. (2)` and `Eq. 2` are the same row. Anything past the first comma points
    *inside* a result, as `Alg. 2, l. 9` does, and belongs in that result's row.
    """
    s = FLAT(s.strip().strip("`")).split(",")[0]
    s = re.sub(r"^§\s*", "Sec. ", s)
    return re.sub(r"\((\d[\d.]*)\)", r"\1", s)


def module_refs(text):
    """The file's bibliography, `{number: entry}`, and where the block sits."""
    m = re.search(r"^## References\s*$(.*?)(?=^-/)", text, re.S | re.M)
    if not m:
        return {}, None
    ents, cur = {}, None
    for line in m.group(1).splitlines():
        e = ENTRY.match(line)
        if e:
            cur = e.group(1)
            ents[cur] = e.group(2).strip()
        elif cur and line.strip():
            ents[cur] += " " + line.strip()
    return ents, m.span()


def cites_of(path):
    """`{entry: {locator}}` for one Lean file; the bare cite gives locator ""."""
    text = path.read_text(encoding="utf-8", errors="replace")
    ents, span = module_refs(text)
    if not ents:
        return {}
    body = text[: span[0]] + text[span[1] :]
    found = {}
    for m in CITE.finditer(body):
        entry = ents.get(m.group(1))
        if entry is None:
            continue  # `check-conventions.sh` is what complains about this
        loc = (m.group(2) or "").strip(", ").strip()
        found.setdefault(entry, set()).add(locator(loc) if LOCATOR.match(loc) else "")
    for entry in ents.values():
        found.setdefault(entry, set())
    return found


def rows_of(table):
    """The body rows of the first markdown table in `table`, as cell lists."""
    rows = []
    for line in table.splitlines():
        line = line.strip()
        if not line.startswith("|"):
            continue
        # `\|` is an escaped pipe inside a cell, not a cell boundary.
        cells = [c.strip().replace("\\|", "|")
                 for c in re.split(r"(?<!\\)\|", line.strip("|"))]
        if all(set(c) <= set("-: ") for c in cells):
            continue  # the `|---|` separator
        rows.append(cells)
    return rows


class Paper:
    """One `references/*.md`: the canonical entry, and a row per result."""

    def __init__(self, path, say):
        self.path = path
        self.name = path.name
        text = path.read_text(encoding="utf-8")
        head = text.split("\n## ", 1)[0]

        m = re.match(r"#\s+(.+?)\n\s*\n(.+?)(?:\n\s*\n|\Z)", head, re.S)
        if not m:
            say(f"{self.rel}:1: opens with `# <title>`, a blank line, then the "
                "bibliography entry as one paragraph")
            self.title, self.entry = path.stem, ""
        else:
            self.title, self.entry = m.group(1).strip(), FLAT(m.group(2))

        for field in ("Source", "Inventory"):
            if f"**{field}:**" not in head:
                say(f"{self.rel}:1: no `**{field}:**` line")

        self.inventory = ""
        m = re.search(r"\*\*Inventory:\*\*\s*(confirmed|partial|unconfirmed)", head)
        if m:
            self.inventory = m.group(1)
        elif "**Inventory:**" in head:
            say(f"{self.rel}:1: `**Inventory:**` is one of confirmed, partial, "
                "unconfirmed")

        m = re.search(r"^## Cited without a result\s*$(.*?)(?=^## |\Z)", text, re.S | re.M)
        self.general = set(LINK.findall(m.group(1))) if m else None

        self.results = {}
        m = re.search(r"^## Results\s*$(.*?)(?=^## |\Z)", text, re.S | re.M)
        if not m:
            say(f"{self.rel}:1: no `## Results` section")
            return
        for cells in rows_of(m.group(1)):
            if len(cells) != 3:
                say(f"{self.rel}: `## Results` rows have three cells "
                    f"(result, what it says, in CORALean): {cells[0][:40]}")
                continue
            result, _, where = cells
            if result.lower() == "result":
                continue  # the header
            result = locator(result)
            if result in self.results:
                say(f"{self.rel}: `{result}` is listed twice")
            # Only a link at a Lean file is a formalization; an `n/a` note may
            # well link the page where the result is really tracked.
            links = [l for l in LINK.findall(where) if l.endswith(".lean")]
            planned = where.strip() in {"—", "-"}
            excluded = where.startswith("n/a")
            if links and planned:
                say(f"{self.rel}: `{result}` is both linked and marked unformalized")
            elif excluded:
                links = []
            elif not links and not planned:
                say(f"{self.rel}: `{result}`: the third cell is a link to the "
                    "formalization, `—` for in scope and not done, or `n/a — <why>`")
            self.results[result] = links if links else (None if excluded else [])

    @property
    def rel(self):
        return self.path.relative_to(ROOT)

    @property
    def counted(self):
        """Rows in scope: an `n/a` row is out of scope and out of the count."""
        return [v for v in self.results.values() if v is not None]

    @property
    def excluded(self):
        """Rows the table puts outside the count, each saying why."""
        return [v for v in self.results.values() if v is None]

    @property
    def done(self):
        return [v for v in self.counted if v]

    @property
    def status(self):
        n, d, x = len(self.done), len(self.counted), len(self.excluded)
        if d == 0:
            # Nothing in scope is complete, not unknown — unless the table is
            # empty, which means the paper has not been read.
            return ("🟢" if x else "⚪"), n, d, x
        return ("🟢" if n == d else "🔴" if n == 0 else "🟡"), n, d, x


def main():
    problems = []
    say = problems.append

    if not REFS.is_dir():
        print(f"no {REFS.relative_to(ROOT)}/ directory", file=sys.stderr)
        return 1

    # One directory per year, so the pages sort by year and then by name.
    papers = [Paper(p, say) for p in sorted(REFS.glob("*/*.md"))]

    by_entry = {}
    for paper in papers:
        if not paper.entry:
            continue
        if paper.entry in by_entry:
            say(f"{paper.rel}: the same bibliography entry is also in "
                f"{by_entry[paper.entry].name}")
        by_entry[paper.entry] = paper

    # --- the tree against `references/` ------------------------------------- #

    cited = {}  # entry -> {locator: {file}}
    for path in sorted(SRC.rglob("*.lean")):
        for entry, locs in cites_of(path).items():
            if entry.startswith("`"):
                continue  # an in-repo cross-reference or a CORA source file
            cited.setdefault(entry, {})
            for loc in locs:
                cited[entry].setdefault(loc, set()).add(path)

    for entry, locs in sorted(cited.items()):
        paper = by_entry.get(entry)
        if paper is None:
            where = sorted({str(p.relative_to(ROOT)) for s in locs.values() for p in s})
            near = [p.name for p in papers if p.entry and p.entry[:25] == entry[:25]]
            say(f"{where[0]}: cites a publication with no file in references/: "
                f"{entry[:70]}…" + (f" (did you mean {near[0]}?)" if near else ""))
            continue
        for loc, files in sorted(locs.items()):
            if not loc or loc in paper.results:
                continue
            first = sorted(str(f.relative_to(ROOT)) for f in files)[0]
            say(f"{first}: cites `{loc}`, which is not a row in {paper.name}")

        # A file citing the paper and naming no result is in no row, so it would
        # otherwise be invisible here — and a paper leant on by twenty files that
        # names none of its results is worth seeing.
        bare = {p for p in locs.get("", set()) if not any(
            loc and p in fs for loc, fs in locs.items())}
        want = {str(p.relative_to(ROOT)) for p in bare}
        if not want:
            if paper.general is not None:
                say(f"{paper.rel}: has a `## Cited without a result` section, but "
                    "every file citing this paper names one")
            continue
        if paper.general is None:
            say(f"{paper.rel}: {len(want)} file(s) cite this paper without naming a "
                "result; list them under `## Cited without a result`")
            continue
        got = {str((paper.path.parent / l).resolve().relative_to(ROOT))
               for l in paper.general}
        for miss in sorted(want - got):
            say(f"{paper.rel}: `## Cited without a result` omits {miss}")
        for extra in sorted(got - want):
            say(f"{paper.rel}: `## Cited without a result` lists {extra}, which "
                "does not cite this paper without a result")

    # --- `references/` against the tree ------------------------------------- #

    for paper in papers:
        for result, links in sorted(paper.results.items()):
            for link in links or []:
                target = (paper.path.parent / link).resolve()
                if not target.exists():
                    say(f"{paper.rel}: `{result}` links {link}, which does not exist")
                    continue
                if target.suffix != ".lean":
                    continue
                if paper.entry not in cites_of(target):
                    say(f"{paper.rel}: `{result}` links {target.name}, which does "
                        "not cite this paper")

    # --- findings ------------------------------------------------------------ #

    # An error in a paper lives on that paper's page, beside the result. The
    # index lists which pages have one, so the overview survives the split.
    with_findings = {str(p.rel.relative_to(REFS.name)) for p in papers
                     if re.search(r"^## Findings\s*$", p.path.read_text(encoding="utf-8"),
                                  re.M)}
    readme_text = (REFS / "README.md").read_text(encoding="utf-8") if \
        (REFS / "README.md").exists() else ""
    m = re.search(r"^## Findings\s*$(.*?)(?=^## |\Z)", readme_text, re.S | re.M)
    # links out of `references/` in that section are prose, not entries
    listed_findings = {l for l in (LINK.findall(m.group(1)) if m else [])
                       if not l.startswith("../")}
    for miss in sorted(with_findings - listed_findings):
        say(f"references/README.md: {miss} has a `## Findings` section and is not "
            "listed under `## Findings` here")
    for extra in sorted(listed_findings - with_findings):
        say(f"references/README.md: lists {extra} under `## Findings`, but that page "
            "has no `## Findings` section")

    findings = ROOT / "FINDINGS.md"
    if findings.exists() and "## Errors and omissions in the sources" in \
            findings.read_text(encoding="utf-8"):
        say("FINDINGS.md: an error in a paper belongs on that paper's page under "
            "references/, not here")

    # --- the README against both -------------------------------------------- #

    readme = REFS / "README.md"
    if not readme.exists():
        say("references/README.md: missing — it is the index")
    else:
        text = readme.read_text(encoding="utf-8")
        m = re.search(r"^\|.*\n(?:\|.*\n)+", text, re.M)
        listed = []
        for cells in rows_of(m.group(0)) if m else []:
            links = LINK.findall(cells[0])
            if not links:
                continue
            listed.append((links[0], cells[-1]))
        want = [str(p.rel.relative_to(REFS.name)) for p in papers]
        got = [name for name, _ in listed]
        if got != want:
            missing = [n for n in want if n not in got]
            extra = [n for n in got if n not in want]
            if missing:
                say("references/README.md: not listed: " + ", ".join(missing))
            if extra:
                say("references/README.md: listed but no such file: " + ", ".join(extra))
            if not missing and not extra:
                say("references/README.md: rows are in a different order from the "
                    "files, which sort by year")
        for name, cell in listed:
            paper = next(
                (p for p in papers if str(p.rel.relative_to(REFS.name)) == name), None)
            if paper is None:
                continue
            m = STATUS.match(cell)
            if not m:
                say(f"references/README.md: {name}: last cell reads `🟢 5/5 | 4` — "
                    "an emoji, formalized over in scope, then how many are out of it")
                continue
            emoji, n, d, x = paper.status
            got = (m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4)))
            if got != (emoji, n, d, x):
                say(f"references/README.md: {name}: says {cell}, but the file has "
                    f"{emoji} {n}/{d} | {x}")

    for line in problems:
        print(line)
    total = sum(len(p.counted) for p in papers)
    done = sum(len(p.done) for p in papers)
    out = sum(len(p.excluded) for p in papers)
    if problems:
        print(f"references: {len(problems)} problem(s)")
        return 1
    print(f"references: {len(papers)} papers, {done}/{total} results formalized, "
          f"{out} out of scope, all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
