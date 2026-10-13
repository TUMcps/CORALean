#!/usr/bin/env python3
"""Checks `references/` against the tree, so a coverage table cannot rot.

    python3 scripts/check-references.py
    python3 scripts/check-references.py --fix   # rewrite stale README counts

`references/` holds one file per publication, listing that paper's numbered
results and, for each, where it is formalized. Nothing here reads Lean: the
cites are in module docstrings, which `check-conventions.sh` already keeps
well-formed. What this adds is that the two agree — every paper cited has a
file, every link resolves and points at a file that cites that very result,
every row asserting something links a file that proves something,
every result cited somewhere is a row, every result one page defers to another
is a row there, and the README's counts are the counts.

Every row also carries a `Class` cell, which `scripts/formalization-stats.py`
turns into the paper's figure. A row in scope and formalized says how the *paper's*
statement fared (`correct`, `underspecified`, `proof-gap`, `fixed`, `false`), and
everything but `correct` gives its reason in the cell; a row out of scope says
why (`restated`, `mathlib`, `not-a-claim`, `done-differently`, `not-covered`),
the five reasons the README allows; a row in scope and not yet formalized is `—`.
A `correct` row is formalized *as printed*, so its note may not use the vocabulary of a
departure (`HEDGE`) unless an `**As printed:**` marker says why the printed statement
follows all the same.

`fixed` and `underspecified` are told apart by the input the printed statement fails on
(#120). `fixed`: the statement is false on a NON-DEGENERATE input -- one the paper's setting
admits, not an empty set, zero dimension, zero generators, a zero norm or the like -- and
the formalization proves the corrected statement. `underspecified`: not false in the
paper's setting, or false only on a degenerate input the paper's conventions exclude (the
note then names the hypothesis supplied), or a typo, a missing index, a listing that
needs a bound. A `fixed` row backs its claim with a Lean counterexample: its third cell
says `**Counterexample:** `Decl`` for a theorem the row's linked files declare (a theorem,
so no `sorry` and no axiom, which `check-axioms.sh` sees). The rare row for which none is
written says `**No counterexample:** <why>` instead, the reason at least 40 characters.
The committed `experiments/paper/formalization-stats.json` must be what that
script would write now, so the figure cannot lag the tables.

`references/coverage/` is the other half: one table per CORA class, one row per CORA
method (`contSet/@zonotope/plus.m`, ...), saying whether CORALean answers it
(`proved`, `float`, `—`, or `out-of-scope` with one of a few documented reasons).
Every method file of every listed class must have a row; every linked declaration
must exist in the linked file; a `proved` row must link a theorem and a `float`
row a float-layer theorem. The method inventory is committed
(`references/coverage/cora-inventory.json`) so CI needs no CORA checkout, and is
compared with one when `CORA_DIR` (default `~/CORA`) exists. See
`references/coverage/README.md`.

Exit status is 1 on any complaint, so it belongs in CI beside the conventions.
`--fix` writes the counts it computed into the README's cells in place of the
stale ones, so a count is never typed by hand; every other complaint it only
reports, since each of those is a judgement about a page.
"""
import json
import os
import re
import sys
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
REFS = ROOT / "references"

# A `## References` entry, `* [1] ...`, continued by any indented line under it.
ENTRY = re.compile(r"^\s*\*\s*\[(\d+)\]\s*(.*)$")
# A cite, `[1]` or `[1, Prop. 3.3]`. The locator is kept only when it looks like
# one: `[0, r]` is an interval and `[1, 2]` a pair of cites, neither a result.
CITE = re.compile(r"\[(\d+)((?:,\s*)[^\]\n]*)?\]")
LOCATOR = re.compile(
    r"^(Thm\.|Prop\.|Property|Lemma|Def\.|Cor\.|Sec\.|Eq\.|Alg\.|Ch\.|Table|Fig\.|Remark|"
    r"Heuristic|Assumption|Example|App\.|§|pp?\.)", re.I
)
LINK = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
# A row that asserts something, as against one naming a definition, a section or
# an algorithm. Only these are held to linking a file that proves something.
# Exported for use in formalization-stats.py.
CLAIM = re.compile(r"^(Thm\.|Prop\.|Property|Lemma|Cor\.)", re.I)
# A file proves something if it declares a theorem, or discharges a field of a
# structure that carries its own guarantee -- `SupportBound`'s `le := by ...`.
PROOF = re.compile(r"^(theorem|lemma)\s|:=\s*by\b", re.M)
# A cell deferring a result to the page that owns it: ``tracked as `X` on
# [Title](../year/file.md)``. The locator and the page are what get checked.
TRACKED = re.compile(r"tracked as\s+`([^`]+)`\s+on\s+\[[^\]]*\]\(([^)]+)\)")
# A README row: the paper cell links the file, the last cell is the count —
# formalized over in scope, then how many rows sit outside the count entirely.
STATUS = re.compile(r"^(🟢|🟡|🔴|⚪)\s*(\d+)/(\d+)\s*\|\s*(\d+)$")

# What a row says about the *paper's* statement, from the weakest finding up.
# `correct`: formalized as printed. `underspecified`: not false, but a hypothesis,
# definition or index is missing or misprinted and the formalization supplies it.
# `proof-gap`: the statement is formalized as printed, but the printed proof or
# derivation does not establish it. `fixed`: false as printed on a NON-DEGENERATE input
# (not the empty set, dimension 0, zero generators, a zero norm, ...), true after the
# correction the row names, and backed by a Lean counterexample theorem (see
# `COUNTEREXAMPLE`). `false`: false as printed and not repairable in the paper's intent.
# Degenerate edge cases the paper's setting excludes are `underspecified`, whose note
# names the hypothesis the formalization supplies.
VERDICTS = ("correct", "underspecified", "proof-gap", "fixed", "false")
# Why a row sits outside the count; exactly the reasons references/README.md allows.
OUT_OF_SCOPE = ("restated", "mathlib", "not-a-claim", "done-differently", "not-covered")
CLASS = re.compile(r"^`([a-z-]+)`\s*(?:—\s*(.*\S))?$")
# A `correct` row is formalized *as printed*, so its note may not say otherwise. These
# phrases are the textual proxy for a note admitting the Lean theorem is not the printed
# one (#119). A row may still use one where the printed statement follows directly from
# what is proved -- a stronger theorem, a representation that denotes the same set -- and
# then says so after an explicit `**As printed:**` marker, with the reason.
HEDGE = re.compile(r"done differently|no counterpart|not covered|stated at `point`|only the\b|"
                   r"rather than|not the printed|not modell?ed|not transcribed", re.I)
# A row in scope and not done may still say what part of it exists: the Lean files that are
# there are linked (and checked like any link), and `missing:` says what is not.
PARTIAL = re.compile(r"^—\s+partial:\s*\S.*;\s*missing:\s*\S.{9,}$", re.S)
# A running time stated in a result's second cell: `complexity O(n⁵)`, `in O(ph log h)`,
# `in time linear`, `the O(n²) complexity`. Sizes (`O(h) generators`) are not running times
# and pass.
RUNNING_TIME = re.compile(r"complexity\s*`?O\(|\bin `?O\(|in time linear|\bat complexity\b|"
                          r"\bO\([^|\n]*?\)`?\s+complexity\b", re.I)
AS_PRINTED = re.compile(r"\*\*As printed:\*\*\s*(\S.{39,})")
# A `fixed` row names the Lean counterexample theorem(s) in its third cell, or says why
# there is none. The named theorems must be declared in a file the row links.
COUNTEREXAMPLE = re.compile(r"\*\*Counterexample:\*\*\s*((?:`[^`\n]+`(?:\s*,\s*|\s+and\s+)?)+)")
NO_COUNTEREXAMPLE = re.compile(r"\*\*No counterexample:\*\*\s*(\S.{39,})")
STATS_JSON = ROOT / "experiments" / "paper" / "formalization-stats.json"
# One directory per year of publication; `references/coverage/` is the other kind of page.
PAPER_GLOB = "[0-9][0-9][0-9][0-9]/*.md"

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
        self.say = say
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
        self.partials = {}  # Lean files a `— partial:` note links, checked but not counted
        # `{result: (locator, page)}` for the rows that defer to another page.
        self.tracked = {}
        # `{result: (class, reason)}`, see `VERDICTS` and `OUT_OF_SCOPE`.
        self.verdicts = {}
        m = re.search(r"^## Results\s*$(.*?)(?=^## |\Z)", text, re.S | re.M)
        if not m:
            say(f"{self.rel}:1: no `## Results` section")
            return
        for cells in rows_of(m.group(1)):
            if len(cells) != 4:
                say(f"{self.rel}: `## Results` rows have four cells (result, what it "
                    f"says, in CORALean, class): {cells[0][:40]}")
                continue
            result, says, where, klass = cells
            if result.lower() == "result":
                continue  # the header
            result = locator(result)
            if result in self.results:
                say(f"{self.rel}: `{result}` is listed twice")
            # Only a link at a Lean file is a formalization; an `n/a` note may
            # well link the page where the result is really tracked.
            links = [l for l in LINK.findall(where) if l.endswith(".lean")]
            # `—` alone, or `— partial: <what exists, linked>; missing: <what is left>`
            planned = where.strip() in {"—", "-"} or where.strip().startswith("— ")
            excluded = where.startswith("n/a")
            if planned and where.strip() not in {"—", "-"} and not PARTIAL.search(where):
                say(f"{self.rel}: `{result}`: a `—` row with a note reads `— partial: <the "
                    "Lean declarations that exist, linked>; missing: <what is left>`")
            elif links and planned and not PARTIAL.search(where):
                say(f"{self.rel}: `{result}` is both linked and marked unformalized")
            elif excluded:
                links = []
            elif not links and not planned:
                say(f"{self.rel}: `{result}`: the third cell is a link to the "
                    "formalization, `—` for in scope and not done, or `n/a — <why>`")
            tracked = TRACKED.search(where)
            if tracked:
                self.tracked[result] = (locator(tracked.group(1)), tracked.group(2))
            if planned and links:
                self.partials[result] = links
                links = []
            self.results[result] = links if links else (None if excluded else [])
            self.verdicts[result] = self.parse_class(result, klass, excluded,
                                                    bool(links) and not planned)
            if not excluded:
                self.check_complexity(result, says, where)
            if self.verdicts[result][0] == "correct":
                self.check_hedge(result, where)
            elif self.verdicts[result][0] == "fixed":
                self.check_counterexample(result, where, links)

    def parse_class(self, result, cell, excluded, formalized):
        """`(class, reason)` of one row's `Class` cell, complaining when it is
        not one the row's state allows."""
        m = CLASS.match(cell) if cell != "—" else None
        klass, reason = (m.group(1), m.group(2) or "") if m else (cell, "")
        if excluded:
            allowed, hint = OUT_OF_SCOPE, "an out-of-scope row says why"
        elif formalized:
            allowed, hint = VERDICTS, "a formalized row says how the paper's statement fared"
        else:
            allowed, hint = ("—",), "a row in scope and not yet formalized is `—`"
        if klass not in allowed:
            self.say(f"{self.rel}: `{result}`: class `{cell[:30]}` is not one of "
                     f"{', '.join(allowed)} ({hint})")
        elif klass in VERDICTS and klass != "correct" and len(reason) < 10:
            self.say(f"{self.rel}: `{result}` is `{klass}`, so its class cell gives the "
                     "reason after a dash: `fixed` — what was wrong and what was done")
        return klass, reason

    def check_counterexample(self, result, where, links):
        """A `fixed` row is false on a non-degenerate input, so it links a Lean theorem
        that says so: `**Counterexample:** `Decl`` with `Decl` a theorem declared in a
        linked file, or `**No counterexample:** <why>` for the rare row without one."""
        m = COUNTEREXAMPLE.search(where)
        if not m:
            if not NO_COUNTEREXAMPLE.search(where):
                self.say(f"{self.rel}: `{result}` is `fixed`, so it names its Lean counterexample "
                         "theorem after `**Counterexample:**` (or says `**No counterexample:** <why>`)")
            return
        declared = set()
        for link in links:
            target = (self.path.parent / link).resolve()
            if target.exists():
                declared |= {n.rsplit(".", 1)[-1] for n, kind, _ in lean_decls(target)
                             if kind in ("theorem", "lemma")}
        for name in re.findall(r"`([^`]+)`", m.group(1)):
            if name.rsplit(".", 1)[-1] not in declared:
                self.say(f"{self.rel}: `{result}`: counterexample `{name}` is not a theorem "
                         "declared in a file the row links")

    def check_complexity(self, result, says, where):
        """A running time printed beside a result is a row of its own, so no row in scope
        (formalized in any class, or `—`) carries one in its second cell (references/README.md, "A complexity statement is a
        row of its own"). A result whose statement *is* the bound links its `Complexity/Time/` file."""
        if RUNNING_TIME.search(says) and "/Complexity/Time/" not in where:
            self.say(f"{self.rel}: `{result}` states a running time in its own row; give it a "
                     f"row `{result} (complexity)` (`not-a-claim`, or `Complexity/Time/` if the result is "
                     "the bound)")

    def check_hedge(self, result, where):
        """A `correct` row's note may not admit that the Lean theorem differs from the
        printed statement, except after an `**As printed:**` marker that says why the
        printed statement follows anyway."""
        m = HEDGE.search(where)
        if m and not AS_PRINTED.search(where):
            self.say(f"{self.rel}: `{result}` is `correct`, but its note says `{m.group(0)}`: "
                     "prove the printed statement, reclassify the row, or say why the printed "
                     "statement follows after `**As printed:**`")

    @property
    def rel(self):
        # POSIX spelling, so `1919\\x.md` on Windows is `1919/x.md`, as in the README's links.
        return PurePosixPath(self.path.relative_to(ROOT).as_posix())

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


def fix_count(text, name, old, new):
    """`text` with the count cell of `name`'s README row reading `new`. A cell's
    `|` is escaped in the file, which `rows_of` undid on the way in."""
    esc = lambda c: c.replace("|", "\\|")
    lines = text.split("\n")
    for i, line in enumerate(lines):
        if f"]({name})" in line and line.rstrip().endswith(f"{esc(old)} |"):
            head = line.rstrip()[: -len(f"{esc(old)} |")]
            lines[i] = f"{head}{esc(new)} |"
    return "\n".join(lines)


def short_label(paper, papers):
    """`Wetzlinger 2023 (fully)`: first author and year from the file name, and its
    second word only where two pages would otherwise read the same."""
    words = paper.path.stem.split("-")
    year = paper.path.parent.name
    clash = [q for q in papers if q.path.stem.split("-")[0] == words[0]
             and q.path.parent.name == year]
    return f"{words[0].capitalize()} {year}" + (f" ({words[1]})" if len(clash) > 1 else "")


def stats(papers):
    """Everything `scripts/formalization-stats.py` writes, as plain data: per paper
    and in total, the rows in scope, the formalized ones by class, and the rows out
    of scope by reason. Nothing here depends on the clock, so a committed copy is
    either current or it is not."""
    def tally(rows):
        by = {k: 0 for k in VERDICTS}
        out = {k: 0 for k in OUT_OF_SCOPE}
        for r in rows:
            k = r[0]
            if k in by:
                by[k] += 1
            elif k in out:
                out[k] += 1
        return by, out

    def tally_by_kind(paper):
        """Separate results into claims and definitions with counts."""
        # Initialize structure with keys for in_scope, formalized, and all verdict classes
        claims = {"in_scope": 0, "formalized": 0}
        defs = {"in_scope": 0, "formalized": 0}
        for k in VERDICTS:
            claims[k] = 0
            defs[k] = 0

        for result, (klass, _) in paper.verdicts.items():
            is_claim = CLAIM.match(result)
            kind = claims if is_claim else defs

            # Track in_scope: anything in p.counted (result has a non-None value in paper.results)
            links = paper.results.get(result)
            if links is not None:
                kind["in_scope"] += 1
                # Track formalized: anything in p.done (has links)
                if links:
                    kind["formalized"] += 1
                    # Only count by class if formalized and it's a verdict class
                    if klass in VERDICTS:
                        kind[klass] += 1

        return claims, defs

    entries = []
    for p in papers:
        by, out = tally(p.verdicts.values())
        claims, defs = tally_by_kind(p)

        # Sanity check: claims + definitions should equal existing totals
        claims_in_scope = claims["in_scope"]
        defs_in_scope = defs["in_scope"]
        if claims_in_scope + defs_in_scope != len(p.counted):
            raise ValueError(f"{p.rel}: claims in_scope {claims_in_scope} + definitions in_scope {defs_in_scope} "
                           f"!= {len(p.counted)} (expected in_scope total)")

        claims_formalized = claims["formalized"]
        defs_formalized = defs["formalized"]
        if claims_formalized + defs_formalized != len(p.done):
            raise ValueError(f"{p.rel}: claims formalized {claims_formalized} + definitions formalized {defs_formalized} "
                           f"!= {len(p.done)} (expected formalized total)")

        entries.append({
            "page": p.rel.relative_to(REFS.name).as_posix(),
            "label": short_label(p, papers),
            "year": int(p.path.parent.name),
            "title": p.title,
            "in_scope": len(p.counted),
            "formalized": len(p.done),
            "not_formalized": len(p.counted) - len(p.done),
            "out_of_scope": len(p.excluded),
            "out_of_scope_by_reason": out,
            "by_class": by,
            "claims": claims,
            "definitions": defs,
            "findings": [{"result": r, "class": k, "reason": why}
                         for r, (k, why) in p.verdicts.items()
                         if k in VERDICTS and k != "correct"],
        })
    tot_by = {k: sum(e["by_class"][k] for e in entries) for k in VERDICTS}
    tot_out = {k: sum(e["out_of_scope_by_reason"][k] for e in entries) for k in OUT_OF_SCOPE}

    # Build totals for claims and definitions
    tot_claims = {"in_scope": 0, "formalized": 0}
    tot_defs = {"in_scope": 0, "formalized": 0}
    for k in VERDICTS:
        tot_claims[k] = 0
        tot_defs[k] = 0

    for e in entries:
        tot_claims["in_scope"] += e["claims"]["in_scope"]
        tot_claims["formalized"] += e["claims"]["formalized"]
        tot_defs["in_scope"] += e["definitions"]["in_scope"]
        tot_defs["formalized"] += e["definitions"]["formalized"]
        for k in VERDICTS:
            tot_claims[k] += e["claims"].get(k, 0)
            tot_defs[k] += e["definitions"].get(k, 0)

    # Sanity check at global level
    if tot_claims["in_scope"] + tot_defs["in_scope"] != sum(e["in_scope"] for e in entries):
        raise ValueError(f"Global: claims in_scope {tot_claims['in_scope']} + definitions in_scope {tot_defs['in_scope']} "
                       f"!= {sum(e['in_scope'] for e in entries)} (expected in_scope total)")

    if tot_claims["formalized"] + tot_defs["formalized"] != sum(e["formalized"] for e in entries):
        raise ValueError(f"Global: claims formalized {tot_claims['formalized']} + definitions formalized {tot_defs['formalized']} "
                       f"!= {sum(e['formalized'] for e in entries)} (expected formalized total)")

    return {
        "classes": list(VERDICTS),
        "out_of_scope_reasons": list(OUT_OF_SCOPE),
        "totals": {
            "papers": len(entries),
            "papers_with_findings": sum(1 for e in entries if e["findings"]),
            "in_scope": sum(e["in_scope"] for e in entries),
            "formalized": sum(e["formalized"] for e in entries),
            "not_formalized": sum(e["not_formalized"] for e in entries),
            "out_of_scope": sum(e["out_of_scope"] for e in entries),
            "out_of_scope_by_reason": tot_out,
            "by_class": tot_by,
            "claims": tot_claims,
            "definitions": tot_defs,
        },
        "papers": entries,
        "cora_coverage": coverage_stats(papers, coverage_tables(lambda m: None)),
    }


# --------------------------------------------------------------------------- #
# CORA coverage: one row per CORA method                                       #
# --------------------------------------------------------------------------- #

COVERAGE = REFS / "coverage"
INVENTORY = COVERAGE / "cora-inventory.json"
# The CORA directories whose classes are tabulated: set representations, continuous
# dynamics, hybrid dynamics and neural networks (`nn/@neuralNetwork`, and `nn/layers/`, one
# row per layer file). `matrixSet/`, `specification/`, `discrDynamics/`, `converter/` and
# `global/` are not part of the count; the README says why.
CORA_GROUPS = ("contSet", "contDynamics", "hybridDynamics", "nn")
# What a row says about a CORA method: a real-layer definition with a theorem about it
# (`proved`), additionally a float-layer computable definition with a theorem (`float`),
# not yet (`—`), or not CORALean's business (`out-of-scope`, with a reason).
CORA_STATES = ("proved", "float", "—", "out-of-scope")
CORA_OUT = ("plotting/display", "random/sampling", "solver-dependent",
            "io/conversion-to-matlab-objects", "matlab-runtime", "deprecated")
# The groups the paper's overview shows, one bar each.
REPORT_GROUP = {"contSet": "contSet", "contDynamics": "contDynamics",
                "hybridDynamics": "hybrid", "nn": "neuralNetworks"}
REPORT_GROUPS = ("contSet", "contDynamics", "hybrid", "neuralNetworks")
# A note is `;`- or sentence-separated parts; a row is a cora-issue row iff one part starts
# `cora-issue —` (wherever it stands in the note), so a leading `route a —` part cannot drop it.
CORA_ISSUE = re.compile(r"(?:^|[;.]\s+)cora-issue\s+—\s*(.{10,})$")
CORA_ISSUE_PART = re.compile(r"(?:^|[;.]\s+)cora-issue")
DECL = re.compile(
    r"^(?:@\[[^\]\n]*\]\s*)*((?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*)"
    r"(def|theorem|lemma|abbrev|structure|inductive|class|instance)\s+(?:\(priority\s*:=\s*\w+\)\s+)?([^\s({\[:]+)", re.M)
COUNTS_BLOCK = re.compile(r"(<!-- coverage-counts -->\n)(.*?)(<!-- /coverage-counts -->)", re.S)


def strip_block_comments(text):
    """`text` without its (nested) `/- ... -/` comments, so a line of Lean quoted in a
    docstring is not a declaration."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return "".join(out)


_DECLS = {}


def lean_decls(path):
    """`[(name, kind, private)]` of the declarations written in one Lean file."""
    path = Path(path)
    if path not in _DECLS:
        text = strip_block_comments(path.read_text(encoding="utf-8", errors="replace"))
        _DECLS[path] = [(m.group(3), m.group(2), "private" in m.group(1))
                        for m in DECL.finditer(text)]
    return _DECLS[path]


def is_float_path(path, name=""):
    p = PurePosixPath(Path(path).as_posix())
    return "Float" in p.parts or "Float" in p.stem or "Float" in name


_ALLOW = None


def noncomputable_allowlist():
    """The names on `scripts/noncomputable-allowlist.txt`."""
    global _ALLOW
    if _ALLOW is None:
        lines = (ROOT / "scripts" / "noncomputable-allowlist.txt").read_text(encoding="utf-8").splitlines()
        _ALLOW = {l.split()[0] for l in lines if l.strip() and not l.startswith("#")}
    return _ALLOW


class CoraTable:
    """One `references/coverage/<group>/<class>.md`: a row per CORA method."""

    def __init__(self, path, say):
        self.path, self.say = path, say
        self.group, self.name = path.parent.name, path.stem
        self.rows = {}   # method -> (state, third cell, note)
        self.issues = 0
        text = path.read_text(encoding="utf-8")
        if not re.match(rf"# {re.escape(self.group)}/@?{re.escape(self.name)}\n", text):
            say(f"{self.rel}:1: opens with `# {self.group}/@{self.name}` (`# nn/layers` for the layer files)")
        for cells in rows_of(text):
            if len(cells) != 4:
                say(f"{self.rel}: rows have four cells (method, state, in CORALean, note): "
                    f"{cells[0][:40]}")
                continue
            method, state, where, note = cells
            if method == "Method":
                continue
            method = method.strip("`")
            if method in self.rows:
                say(f"{self.rel}: `{method}` is listed twice")
            self.rows[method] = (state, where, note)
            if CORA_ISSUE.search(note):
                self.issues += 1
            elif CORA_ISSUE_PART.search(note):
                say(f"{self.rel}: `{method}`: a note part starting `cora-issue` reads "
                    "`cora-issue — <what CORA gets wrong, and where FINDINGS.md says so>`")

    @property
    def rel(self):
        return PurePosixPath(self.path.relative_to(ROOT).as_posix())

    def states(self):
        return [v[0] for v in self.rows.values()]

    def out_reasons(self):
        out = {k: 0 for k in CORA_OUT}
        for state, where, _ in self.rows.values():
            if state == "out-of-scope":
                m = re.match(r"^n/a — (\S+)$", where)
                if m and m.group(1) in out:
                    out[m.group(1)] += 1
        return out

    def check(self, inventory):
        say = self.say
        want = inventory.get(self.group, {}).get(self.name)
        if want is None:
            say(f"{self.rel}: `{self.group}/@{self.name}` is not in {INVENTORY.name}")
        else:
            for m in want:
                if m not in self.rows:
                    say(f"{self.rel}: no row for CORA method `{m}`")
            for m in self.rows:
                if m not in want:
                    say(f"{self.rel}: `{m}` is not a method of `{self.group}/@{self.name}`")
        for method, (state, where, note) in self.rows.items():
            tag = f"{self.rel}: `{method}`"
            if state not in CORA_STATES:
                say(f"{tag}: state `{state}` is not one of {', '.join(CORA_STATES)}")
                continue
            links = LINK.findall(where)
            if state == "out-of-scope":
                m = re.match(r"^n/a — (\S+)$", where)
                if not m or m.group(1) not in CORA_OUT:
                    say(f"{tag}: an out-of-scope row reads `n/a — <reason>`, the reason one of "
                        f"{', '.join(CORA_OUT)}")
                continue
            if state == "—":
                if where != "—":
                    say(f"{tag}: a row not yet done has `—` in the third cell (a definition "
                        "without a theorem goes in the note)")
            elif not links:
                say(f"{tag}: a `{state}` row links the Lean declarations that answer it")
            self.check_links(tag, state, where, note)

    def check_generic(self, tag, found):
        """Route (b) of `float`: no float counterpart, because the definition is generic over the
        scalar (or the set representation) and the theorem is its soundness proof at every
        instance. The checkable half: the linked definitions are not in the real layer, not
        `noncomputable` and not on `noncomputable-allowlist.txt`, and a linked theorem or class
        from outside the real layer names a scalar or a set representation as a parameter."""
        say = self.say
        defs = [(t, n) for t, n, k in found if k not in ("theorem", "lemma")]
        if not defs:
            say(f"{tag}: a `route b` row links the generic definition it runs")
        for t, n in defs:
            if "Real" in t.parts:
                say(f"{tag}: route b, but `{n}` is in the real layer")
            if n in noncomputable_allowlist():
                say(f"{tag}: route b, but `{n}` is on the noncomputable allowlist")
            for m in DECL.finditer(strip_block_comments(t.read_text(encoding="utf-8"))):
                if m.group(3) == n and "noncomputable" in m.group(1):
                    say(f"{tag}: route b, but `{n}` is `noncomputable`")
        generic = re.compile(r"Scalar|FloatOps|ExactScalar|ContSet \(S n\)")
        if not any("Real" not in t.parts and generic.search(t.read_text(encoding="utf-8"))
                   for t, n, k in found):
            say(f"{tag}: route b, but no linked declaration is stated for a generic scalar "
                "or representation")

    def check_scalar_free(self, tag, found):
        """Route (b), scalar-free: the linked definitions hold no scalar and compute nothing
        numeric (`EmptySet`, `Fullspace`), so there is nothing to generalise over. They may sit in
        the real layer and need no generic theorem; they must still be computable: not
        `noncomputable`, not on `noncomputable-allowlist.txt`."""
        say = self.say
        defs = [(t, n) for t, n, k in found if k not in ("theorem", "lemma")]
        if not defs:
            say(f"{tag}: a `route b (scalar-free)` row links the definition it runs")
        for t, n in defs:
            if n in noncomputable_allowlist():
                say(f"{tag}: route b (scalar-free), but `{n}` is on the noncomputable allowlist")
            for m in DECL.finditer(strip_block_comments(t.read_text(encoding="utf-8"))):
                if m.group(3) == n and "noncomputable" in m.group(1):
                    say(f"{tag}: route b (scalar-free), but `{n}` is `noncomputable`")

    def check_links(self, tag, state, where, note):
        """Every link exists and names a declaration the file really has; a `proved`
        row carries a theorem and a `float` row a theorem in the float layer."""
        say = self.say
        found = []  # (target, name, kind)
        for m in re.finditer(r"\[`([^`]+)`\]\(([^)]+)\)", where + " " + note):
            name, link = m.group(1), m.group(2)
            if not link.endswith(".lean"):
                continue
            target = (self.path.parent / link).resolve()
            if not target.exists():
                say(f"{tag}: links {link}, which does not exist")
                continue
            kinds = [k for n, k, priv in lean_decls(target) if n == name and not priv]
            if not kinds:
                say(f"{tag}: `{name}` is not declared in {target.name}")
                continue
            found.append((target, name, kinds[0]))
        carries = [(t, n, k) for t, n, k in found if k in ("theorem", "lemma", "class", "structure")]
        if state in ("proved", "float") and not carries:
            say(f"{tag}: `{state}` needs a linked theorem (or the class whose fields carry "
                "the guarantee); a definition alone is `—`")
        route_b = note.startswith("route b —")
        route_sf = note.startswith("route b (scalar-free) —")
        if (route_b or route_sf) and state != "float":
            say(f"{tag}: a `route b` note belongs on a `float` row")
        if state == "float" and route_sf:
            self.check_scalar_free(tag, found)
        elif state == "float" and route_b:
            self.check_generic(tag, found)
        elif state == "float":
            if not any(is_float_path(t, n) for t, n, k in carries):
                say(f"{tag}: `float` needs a linked theorem in the float layer "
                    "(a `Float/` path, or `Float` in the file or declaration name)")
            if not any(is_float_path(t, n) for t, n, k in found if k not in ("theorem", "lemma")):
                say(f"{tag}: `float` needs a linked float-layer definition")
        if state == "proved" and where.count("float:"):
            say(f"{tag}: lists a float layer, so the state is `float`")


def cora_inventory():
    try:
        return json.loads(INVENTORY.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


def cora_checkout():
    """The CORA checkout the inventory is compared with, if there is one."""
    for cand in (os.environ.get("CORA_DIR"), str(Path.home() / "CORA")):
        if cand and (Path(cand) / "contSet").is_dir():
            return Path(cand)
    return None


def coverage_tables(say):
    return [CoraTable(p, say) for g in CORA_GROUPS for p in sorted((COVERAGE / g).glob("*.md"))]


def counts_of(table):
    st = table.states()
    return {"methods": len(st), "proved": st.count("proved"), "float": st.count("float"),
            "not_yet": st.count("—"), "out_of_scope": st.count("out-of-scope")}


def counts_block(tables):
    lines = ["| Class | Group | Methods | proved | float | not yet | out of scope | CORA issues |",
             "|---|---|---|---|---|---|---|---|"]
    for t in tables:
        c = counts_of(t)
        lines.append(f"| [{t.name}]({t.group}/{t.name}.md) | {t.group} | {c['methods']} | "
                     f"{c['proved']} | {c['float']} | {c['not_yet']} | {c['out_of_scope']} | {t.issues} |")
    return "\n".join(lines) + "\n"


def check_coverage(say, fix=False):
    inventory = cora_inventory()
    if not COVERAGE.is_dir() or not inventory:
        say(f"{COVERAGE.relative_to(ROOT).as_posix()}: missing, or no {INVENTORY.name}")
        return []
    tables = coverage_tables(say)
    have = {(t.group, t.name) for t in tables}
    for g, classes in inventory.items():
        for c in classes:
            if (g, c) not in have:
                say(f"references/coverage/{g}/{c}.md: no table for CORA class `{g}/@{c}`")
    for t in tables:
        t.check(inventory)
    # The inventory against CORA itself, where a checkout exists.
    cora = cora_checkout()
    if cora:
        for g in CORA_GROUPS:
            on_disk = {d.name[1:]: sorted(f.stem for f in d.glob("*.m"))
                       for d in sorted((cora / g).glob("@*")) if d.is_dir()}
            if g == "nn":
                # one row per layer file, however deep; `private/` helpers have none
                on_disk = {"neuralNetwork": on_disk.get("neuralNetwork", []),
                           "layers": sorted(f.stem for f in (cora / "nn" / "layers").rglob("*.m")
                                            if "private" not in f.parts)}
            if on_disk != inventory.get(g, {}):
                a, b = on_disk, inventory.get(g, {})
                diff = sorted(set(a) ^ set(b)) or sorted(c for c in a if a[c] != b.get(c))
                say(f"{INVENTORY.relative_to(ROOT).as_posix()}: differs from {cora}/{g} "
                    f"({', '.join(diff[:5])}); refresh it from the checkout")
    readme = COVERAGE / "README.md"
    if readme.exists():
        text = readme.read_text(encoding="utf-8")
        m = COUNTS_BLOCK.search(text)
        if not m:
            say("references/coverage/README.md: no `<!-- coverage-counts -->` block")
        elif m.group(2) != counts_block(tables):
            if fix:
                readme.write_text(text[:m.start(2)] + counts_block(tables) + text[m.end(2):],
                                  encoding="utf-8")
                print("references/coverage/README.md: rewrote the counts")
            else:
                say("references/coverage/README.md: the counts table is not what the tables "
                    "say; rerun `python3 scripts/check-references.py --fix`")
    else:
        say("references/coverage/README.md: missing")
    return tables


# --------------------------------------------------------------------------- #
# Which CORA class a paper result lands on, and the theorem categories          #
# --------------------------------------------------------------------------- #

SRC_LEAN = SRC / "CORALean"
SET_DIR = {"Zonotope": "zonotope", "Interval": "interval", "PolyZonotope": "polyZonotope",
           "ConPolyZono": "conPolyZono", "ConZonotope": "conZonotope", "ZonoBundle": "zonoBundle",
           "Ellipsoid": "ellipsoid", "Capsule": "capsule", "HPolytope": "polytope",
           "VPolytope": "polytope", "EmptySet": "emptySet", "Fullspace": "fullspace"}
SYS_DIR = {"LinearSys": "linearSys", "LinearSysDT": "linearSysDT", "LinParamSys": "linParamSys",
           "LinParamSysDT": "linParamSys", "NonlinearSys": "nonlinearSys",
           "NonlinearSysDT": "nonlinearSysDT", "NeurNetContrSys": "neurNetContrSys",
           "NeurNetContrSysDT": "neurNetContrSys", "LinearARX": "linearARX", "NonlinearARX": "nonlinearARX",
           "NonlinParamSys": "nonlinParamSys", "NonlinDASys": "nonlinDASys", "OutputEq": "contDynamics", "Reach": "contDynamics"}
# Where a result lands when it is not about one CORA class.
NON_CLASS = ("global", "specification", "examples", "other")


def bucket(path):
    """The CORA class (or `global`, `neuralNetwork`, `specification`) a linked Lean file
    belongs to, from its path: `ContSet/Zonotope/...` is `zonotope`, a conversion
    `ContSet/Conversion/Real/Zonotope_to_Interval.lean` is the source's method, `ContSet/`'s
    own directories and unions and intersections are `contSet`, `HybridDynamics/Parallel`
    is `parallelHybridAutomaton` and the rest of `HybridDynamics/` `hybridAutomaton`."""
    try:
        parts = Path(path).resolve().relative_to(SRC_LEAN).parts
    except ValueError:
        return "other"
    top = parts[0]
    if top == "ContSet" and len(parts) > 1:
        if parts[1] == "Conversion":
            return SET_DIR.get(Path(parts[-1]).stem.split("_to_")[0], "contSet")
        return SET_DIR.get(parts[1], "contSet")
    if top == "ContDynamics" and len(parts) > 1:
        return SYS_DIR.get(parts[1], "contDynamics")
    if top == "HybridDynamics":
        return "parallelHybridAutomaton" if len(parts) > 1 and parts[1] == "Parallel" \
            else "hybridAutomaton"
    return {"Global": "global", "NN": "neuralNetwork", "Specification": "specification",
            "Examples": "examples"}.get(top, "other")


def linked_files(papers):
    """The Lean files some row links, and the files linked by a formalized row."""
    out = set()
    for p in papers:
        for links in [*p.results.values(), *p.partials.values()]:
            for link in links or []:
                t = (p.path.parent / link).resolve()
                if t.exists() and t.suffix == ".lean":
                    out.add(t)
    return out


def theorem_categories(papers):
    """Every public `theorem`/`lemma` under `src/CORALean`, in exactly one of: a float
    refinement (a `Float/` path, or `Float` in the file or declaration name; wins over
    everything), a proof helper (an `aux_*` name), a paper theorem (anything else in a file
    some row links) or a lemma (the rest). `Examples/` is counted apart, not classified."""
    linked = linked_files(papers)
    cat = {"paper": 0, "float": 0, "helper": 0, "lemma": 0}
    examples = 0
    for path in sorted(SRC_LEAN.rglob("*.lean")):
        decls = [(n, k) for n, k, priv in lean_decls(path) if k in ("theorem", "lemma") and not priv]
        if "Examples" in path.relative_to(SRC_LEAN).parts:
            examples += len(decls)
            continue
        for name, _ in decls:
            if is_float_path(path, name):
                cat["float"] += 1
            elif any(seg.startswith("aux_") for seg in name.split(".")):
                cat["helper"] += 1
            elif path.resolve() in linked:
                cat["paper"] += 1
            else:
                cat["lemma"] += 1
    return {**cat, "total": sum(cat.values()), "examples": examples}


def coverage_stats(papers, tables):
    """The CORA coverage and theorem counts as plain data, with the paper findings
    attributed to a CORA class by the file their row links."""
    zero = lambda: {k: 0 for k in VERDICTS}
    found = {}
    for p in papers:
        for result, (klass, _) in p.verdicts.items():
            links = p.results.get(result)
            if not links or klass not in VERDICTS:
                continue
            first = (p.path.parent / links[0]).resolve()
            found.setdefault(bucket(first), zero())[klass] += 1
    classes = []
    for t in tables:
        c = counts_of(t)
        classes.append({
            "group": t.group, "class": t.name, **c,
            "needs_float": c["proved"],
            "out_of_scope_by_reason": t.out_reasons(),
            "cora_issues": t.issues,
            "findings": found.get(t.name, zero()),
        })
    def agg(entries):
        keys = ("methods", "proved", "float", "not_yet", "out_of_scope", "needs_float", "cora_issues")
        out = {k: sum(e[k] for e in entries) for k in keys}
        out["out_of_scope_by_reason"] = {r: sum(e["out_of_scope_by_reason"][r] for e in entries)
                                         for r in CORA_OUT}
        out["findings"] = {k: sum(e["findings"][k] for e in entries) for k in VERDICTS}
        return out
    groups = {g: agg([e for e in classes if REPORT_GROUP[e["group"]] == g])
              for g in REPORT_GROUPS}
    # Results on files that belong to no CORA class.
    elsewhere = {b: found[b] for b in NON_CLASS if b in found}
    return {
        "states": list(CORA_STATES),
        "out_of_scope_reasons": list(CORA_OUT),
        "classes": classes,
        "groups": groups,
        "totals": agg(classes),
        "findings_not_on_a_class": elsewhere,
        "theorems": theorem_categories(papers),
    }


def main():
    problems = []
    say = problems.append

    if not REFS.is_dir():
        print(f"no {REFS.relative_to(ROOT).as_posix()}/ directory", file=sys.stderr)
        return 1

    # One directory per year, so the pages sort by year and then by name.
    papers = [Paper(p, say) for p in sorted(REFS.glob(PAPER_GLOB))]

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
            where = sorted({p.relative_to(ROOT).as_posix() for s in locs.values() for p in s})
            near = [p.name for p in papers if p.entry and p.entry[:25] == entry[:25]]
            say(f"{where[0]}: cites a publication with no file in references/: "
                f"{entry[:70]}…" + (f" (did you mean {near[0]}?)" if near else ""))
            continue
        for loc, files in sorted(locs.items()):
            if not loc or loc in paper.results:
                continue
            first = sorted(f.relative_to(ROOT).as_posix() for f in files)[0]
            say(f"{first}: cites `{loc}`, which is not a row in {paper.name}")

        # A file citing the paper and naming no result is in no row, so it would
        # otherwise be invisible here — and a paper leant on by twenty files that
        # names none of its results is worth seeing.
        bare = {p for p in locs.get("", set()) if not any(
            loc and p in fs for loc, fs in locs.items())}
        want = {p.relative_to(ROOT).as_posix() for p in bare}
        if not want:
            if paper.general is not None:
                say(f"{paper.rel}: has a `## Cited without a result` section, but "
                    "every file citing this paper names one")
            continue
        if paper.general is None:
            say(f"{paper.rel}: {len(want)} file(s) cite this paper without naming a "
                "result; list them under `## Cited without a result`")
            continue
        got = {(paper.path.parent / l).resolve().relative_to(ROOT).as_posix()
               for l in paper.general}
        for miss in sorted(want - got):
            say(f"{paper.rel}: `## Cited without a result` omits {miss}")
        for extra in sorted(got - want):
            say(f"{paper.rel}: `## Cited without a result` lists {extra}, which "
                "does not cite this paper without a result")

    # --- `references/` against the tree ------------------------------------- #

    for paper in papers:
        for result, links in sorted({**paper.results, **paper.partials}.items()):
            targets = []
            for link in links or []:
                target = (paper.path.parent / link).resolve()
                if not target.exists():
                    say(f"{paper.rel}: `{result}` links {link}, which does not exist")
                    continue
                if target.suffix != ".lean":
                    continue
                cites = cites_of(target)
                if paper.entry not in cites:
                    say(f"{paper.rel}: `{result}` links {target.name}, which does "
                        "not cite this paper")
                    continue
                targets.append(target)
                if locator(result) not in cites[paper.entry]:
                    named = sorted(l for l in cites[paper.entry] if l)
                    says = f"cites {', '.join(named)}" if named else "cites it bare"
                    say(f"{paper.rel}: `{result}` links {target.name}, which {says} "
                        f"— a link is a claim that the file answers to `{result}`")
            if targets and CLAIM.match(result) and not any(
                    PROOF.search(t.read_text(encoding="utf-8", errors="replace"))
                    for t in targets):
                say(f"{paper.rel}: `{result}` asserts something, and links only "
                    f"{', '.join(t.name for t in targets)}, which prove nothing. A "
                    "citation in a docstring is not a proof")

    # --- one page against another -------------------------------------------- #

    # A row belonging to an earlier paper says so and points at that paper's
    # page. The pointer is a claim about the other table, so it is checked the
    # way a link into the tree is: the page has to be here and the row it names
    # has to be on it. Not that the row is *filled* — deferring to a result
    # openly marked `—` is exactly right, and demanding otherwise would force a
    # true statement out of the tree.
    by_path = {p.path.resolve(): p for p in papers}
    pointers = {}
    for paper in papers:
        for result, (loc, link) in sorted(paper.tracked.items()):
            other = by_path.get((paper.path.parent / link).resolve())
            if other is None:
                say(f"{paper.rel}: `{result}` is tracked on {link}, which is not a "
                    "page under references/")
            elif loc not in other.results:
                say(f"{paper.rel}: `{result}` is tracked as `{loc}` on {other.name}, "
                    "which has no such row")
            else:
                pointers[(paper, result)] = (other, loc)

    # Following the pointers has to end at the row that owns the result, and a
    # chain returning to a row it has already been at never does.
    reported = set()
    for start in list(pointers):
        node, seen = start, {start}
        while node in pointers:
            node = pointers[node]
            if node in seen:
                if node not in reported:
                    reported.add(node)
                    say(f"{node[0].rel}: `{node[1]}` is tracked in a cycle, so the "
                        "chain names no page that owns it")
                break
            seen.add(node)

    # --- findings ------------------------------------------------------------ #

    # An error in a paper lives on that paper's page, beside the result. The
    # index lists which pages have one, so the overview survives the split.
    with_findings = {p.rel.relative_to(REFS.name).as_posix() for p in papers
                     if re.search(r"^## Findings\s*$", p.path.read_text(encoding="utf-8"),
                                  re.M)}
    readme_text = (REFS / "README.md").read_text(encoding="utf-8") if \
        (REFS / "README.md").exists() else ""
    m = re.search(r"^## Findings\s*$(.*?)(?=^## |\Z)", readme_text, re.S | re.M)
    # links out of `references/` in that section are prose, not entries
    listed_findings = {l for l in (LINK.findall(m.group(1)) if m else [])
                       if not l.startswith("../")}
    # A paper error is recorded beside the result, so a page claiming one has to
    # have the section the README indexes.
    for paper in papers:
        bad = sorted(r for r, (k, _) in paper.verdicts.items()
                     if k in VERDICTS and k != "correct")
        if bad and paper.rel.relative_to(REFS.name).as_posix() not in with_findings:
            say(f"{paper.rel}: {', '.join('`' + b + '`' for b in bad[:3])} is not "
                "`correct`, and the page has no `## Findings` section to say why")
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
        fixed = []
        m = re.search(r"^\|.*\n(?:\|.*\n)+", text, re.M)
        listed = []
        for cells in rows_of(m.group(0)) if m else []:
            links = LINK.findall(cells[0])
            if not links:
                continue
            listed.append((links[0], cells[-1]))
        want = [p.rel.relative_to(REFS.name).as_posix() for p in papers]
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
                (p for p in papers if p.rel.relative_to(REFS.name).as_posix() == name), None)
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
                if "--fix" in sys.argv[1:]:
                    text = fix_count(text, name, cell, f"{emoji} {n}/{d} | {x}")
                    fixed.append(name)
                    continue
                say(f"references/README.md: {name}: says {cell}, but the file has "
                    f"{emoji} {n}/{d} | {x}")
        if fixed:
            readme.write_text(text, encoding="utf-8")
            print("references/README.md: rewrote the count of " + ", ".join(fixed))

    # --- CORA coverage ------------------------------------------------------ #

    check_coverage(say, fix="--fix" in sys.argv[1:])

    # The committed statistics are a function of the tables, so they are checked
    # rather than trusted: regenerate with `python3 scripts/formalization-stats.py`.
    want = stats(papers)
    try:
        have = json.loads(STATS_JSON.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        have = None
    if have != want:
        say(f"{STATS_JSON.relative_to(ROOT).as_posix()}: missing or stale — rerun "
            "`python3 scripts/formalization-stats.py`")

    for line in problems:
        print(line)
    total = sum(len(p.counted) for p in papers)
    done = sum(len(p.done) for p in papers)
    out = sum(len(p.excluded) for p in papers)
    if problems:
        print(f"references: {len(problems)} problem(s)")
        return 1
    cov = want["cora_coverage"]["totals"]
    print(f"coverage: {cov['methods']} CORA methods: {cov['proved']} proved, {cov['float']} float, "
          f"{cov['not_yet']} not yet, {cov['out_of_scope']} out of scope")
    by = want["totals"]["by_class"]
    print(f"references: {len(papers)} papers, {done}/{total} results formalized, "
          f"{out} out of scope, all checks passed")
    print("references: formalized as " + ", ".join(f"{k} {by[k]}" for k in VERDICTS) +
          "; out of scope as " + ", ".join(
              f"{k} {v}" for k, v in want["totals"]["out_of_scope_by_reason"].items()))
    return 0


if __name__ == "__main__":
    sys.exit(main())
