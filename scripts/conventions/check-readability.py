#!/usr/bin/env python3
"""Readability of every tracked markdown file (CONTRIBUTING.md, "Writing").

Three rules, no allowlist and no exception path:

  paragraph  a prose paragraph is at most 15 lines, a list item at most 8
  cell       the prose of a table cell, link targets `](...)` removed, is at most
             900 characters
  sentence   a sentence has at most 60 words (an inline code span counts as one
             word) and at most 2 semicolons

Fenced code blocks are skipped. Headings, rules and HTML comments are not prose.

  python3 scripts/conventions/check-readability.py            every tracked .md
  python3 scripts/conventions/check-readability.py FILE...    only those files
  python3 scripts/conventions/check-readability.py --index FILE...
                                                              the staged (index) versions of those
                                                              files, for the pre-commit hook
  python3 scripts/conventions/check-readability.py --count    totals per rule

Each message is `file:line: rule: what is wrong`. Exit status 1 if there is one.
"""

import re
import subprocess
import sys
from pathlib import Path

MAX_PARAGRAPH_LINES = 15
MAX_ITEM_LINES = 8
MAX_CELL_CHARS = 900
MAX_SENTENCE_WORDS = 60
MAX_SENTENCE_SEMICOLONS = 2

REPO = Path(__file__).resolve().parents[2]

LIST_ITEM = re.compile(r"^\s*(?:[-*+]|\d+[.)])\s+")
FENCE = re.compile(r"^\s*(```|~~~)")
CODE_SPAN = re.compile(r"(`+)(?:(?!\1).)+?\1", re.S)
LINK_TARGET = re.compile(r"\]\([^)]*\)")
ABBREVIATIONS = {
    "prop", "thm", "alg", "cor", "lem", "def", "eq", "eqs", "sec", "fig", "rem", "ex",
    "ch", "vs", "cf", "e.g", "i.e", "no", "p", "pp", "vol", "ref", "refs", "approx",
    "resp", "incl", "def", "defs", "props", "thms", "algs", "cors", "lems", "sect",
    "tab", "dr", "st", "al",
}
CODE = "\x00"


def split_cells(row):
    """The cells of a table row, honouring `\\|` and code spans."""
    row = row.strip()
    if row.startswith("|"):
        row = row[1:]
    if row.endswith("|") and not row.endswith("\\|"):
        row = row[:-1]
    cells, cur, i, tick = [], [], 0, 0
    while i < len(row):
        c = row[i]
        if c == "\\" and i + 1 < len(row):
            cur.append(row[i:i + 2])
            i += 2
            continue
        if c == "`":
            j = i
            while j < len(row) and row[j] == "`":
                j += 1
            tick = j - i if tick == 0 else (0 if tick == j - i else tick)
            cur.append(row[i:j])
            i = j
            continue
        if c == "|" and tick == 0:
            cells.append("".join(cur))
            cur = []
        else:
            cur.append(c)
        i += 1
    cells.append("".join(cur))
    return cells


def is_separator(row):
    return re.fullmatch(r"\s*\|?[\s:|-]+\|?\s*", row) is not None and "-" in row


def prose(text):
    """Text with link targets removed (for lengths)."""
    return LINK_TARGET.sub("]", text)


def mask(text):
    """`text` with every code span, link target and HTML tag overwritten by `x`, character for
    character (newlines kept), so an offset in the result is an offset in `text` and a code span
    counts as one word."""
    def blank(m):
        return re.sub(r"[^\n]", "x", m.group(0))
    text = CODE_SPAN.sub(blank, text)
    text = LINK_TARGET.sub(lambda m: "](" + re.sub(r"[^\n]", "x", m.group(0)[2:-1]) + ")", text)
    return re.sub(r"<[^>\n]*>", lambda m: " " * len(m.group(0)), text)


BOUNDARY = re.compile(r"[.?!]+[\])*_\"']*\s+(?=[A-Za-z(\[*_$\"\u201c`0-9])")


def sentence_spans(masked):
    """`[(start, end)]` of the sentences of masked text. A full stop ends a sentence unless an
    abbreviation (`Prop.`, `e.g.`), an initial or a number's point comes before it."""
    out, start = [], 0
    for m in BOUNDARY.finditer(masked):
        before = masked[start:m.start()]
        word = re.search(r"(?:^|[\s(\[*_])([\w.'\u2019-]+)$", before)
        raw_w = word.group(1) if word else ""
        w = raw_w.lower()
        nxt = masked[m.end():m.end() + 1]
        if m.group(0).startswith(".") and (w in ABBREVIATIONS
                                           or re.fullmatch(r"[A-Z]", raw_w) is not None
                                           or re.fullmatch(r"[a-z]\.[a-z]", w)
                                           or nxt.isdigit() or nxt == "`"):
            continue
        out.append((start, m.start() + 1))
        start = m.end()
    if start < len(masked):
        out.append((start, len(masked)))
    return out


def sentences(text):
    masked = mask(text)
    return [(masked.count("\n", 0, s), masked[s:e], text[s:e]) for s, e in sentence_spans(masked)]


def words(sentence):
    return len([t for t in sentence.split() if re.search(r"\w", t)])


def check_sentences(text, where, report):
    for off, s, raw in sentences(text):
        w = words(s)
        sc = s.count(";")
        snippet = " ".join(raw.split())[:60]
        if w > MAX_SENTENCE_WORDS:
            report(where + off, "sentence", f"{w} words (at most {MAX_SENTENCE_WORDS}): "
                   f"{snippet}...")
        if sc > MAX_SENTENCE_SEMICOLONS:
            report(where + off, "sentence", f"{sc} semicolons (at most {MAX_SENTENCE_SEMICOLONS}): "
                   f"{snippet}...")


def check_file(path, lines, report):
    def rep(line, rule, msg):
        report(path, line, rule, msg)

    i, n, fence = 0, len(lines), None
    while i < n:
        line = lines[i]
        m = FENCE.match(line)
        if fence:
            if m and m.group(1) == fence:
                fence = None
            i += 1
            continue
        if m:
            fence = m.group(1)
            i += 1
            continue
        stripped = line.strip()
        if not stripped or stripped.startswith("#") or re.fullmatch(r"[-*_]{3,}", stripped):
            i += 1
            continue
        if stripped.startswith("<!--"):
            while i < n and "-->" not in lines[i]:
                i += 1
            i += 1
            continue
        if stripped.startswith("|"):
            if not is_separator(line):
                for cell in split_cells(line):
                    p = prose(cell).strip()
                    if len(p) > MAX_CELL_CHARS:
                        rep(i + 1, "cell", f"table cell has {len(p)} characters "
                            f"(at most {MAX_CELL_CHARS}): {' '.join(p.split())[:50]}...")
                    check_sentences(cell, i + 1, lambda ln, r, m_: rep(ln, r, m_))
            i += 1
            continue
        # a paragraph or a list item: this line plus its continuation lines
        item = LIST_ITEM.match(line) is not None
        j = i + 1
        while j < n:
            nxt = lines[j]
            ns = nxt.strip()
            if (not ns or LIST_ITEM.match(nxt) or FENCE.match(nxt) or ns.startswith("|")
                    or ns.startswith("#") or ns.startswith("<!--")):
                break
            j += 1
        count = j - i
        block = "\n".join(lines[i:j])
        if item:
            if count > MAX_ITEM_LINES:
                rep(i + 1, "paragraph", f"list item has {count} lines (at most {MAX_ITEM_LINES})")
        elif count > MAX_PARAGRAPH_LINES:
            rep(i + 1, "paragraph", f"paragraph has {count} lines (at most {MAX_PARAGRAPH_LINES})")
        # a hard line break (two trailing spaces) ends a sentence
        start = i
        for k in range(i, j):
            if k == j - 1 or lines[k].endswith("  "):
                check_sentences("\n".join(lines[start:k + 1]), start + 1,
                                lambda ln, r, m_: rep(ln, r, m_))
                start = k + 1
        i = j


def tracked_markdown():
    """Every tracked `.md`. Without a repository or without `git` (the CI image) every file is."""
    try:
        run = subprocess.run(["git", "ls-files", "*.md"], cwd=REPO, capture_output=True, text=True)
        if run.returncode == 0:
            return run.stdout.split()
    except FileNotFoundError:
        pass
    skip = {".git", ".lake", "node_modules"}
    return sorted(str(p.relative_to(REPO)) for p in REPO.rglob("*.md")
                  if not skip & set(p.relative_to(REPO).parts))


def index_text(path):
    return subprocess.run(["git", "show", f":{path}"], cwd=REPO, capture_output=True, text=True,
                          check=True, encoding="utf-8").stdout


def main(argv):
    count = "--count" in argv
    index = "--index" in argv
    files = [a for a in argv if not a.startswith("--")]
    if not files:
        files = tracked_markdown()
    msgs = []
    totals = {"paragraph": 0, "cell": 0, "sentence": 0}

    def report(path, line, rule, msg):
        totals[rule] += 1
        msgs.append(f"{path}:{line}: {rule}: {msg}")

    for f in files:
        if index:
            text = index_text(f)
        else:
            p = REPO / f if not Path(f).is_absolute() else Path(f)
            if not p.exists():
                continue
            text = p.read_text(encoding="utf-8")
        rel = f
        check_file(rel, text.split("\n"), report)
    if count:
        print(totals)
        return 0
    for m in msgs:
        print(m)
    if msgs:
        print(f"check-readability: {len(msgs)} problems (paragraph {totals['paragraph']}, "
              f"cell {totals['cell']}, sentence {totals['sentence']})", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
