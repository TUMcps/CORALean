#!/usr/bin/env python3
"""Rewrites the `## References` entries of the Lean modules to the rendering of their page (#265).

    python3 scripts/paper/render-references.py          # rewrite every entry that differs
    python3 scripts/paper/render-references.py --check  # list the files it would rewrite, change nothing

Each `references/<year>/*.md` page carries one BibTeX entry (see `scripts/paper/refentry.py`), and a
module docstring cites the publication with a numbered line under `## References`,

    * [1] [<authors>. "<Title>". <Venue>, <year>.](<relative path to the page>)

The whole line is a markdown link to the page, the path computed from the file's depth (#237).

`<authors>` is `A. Name, B. Name and C. Name`, the title and the venue are the entry's with the
protecting braces dropped, wrapped at the line limit with a six-space hanging indent. An entry
is found by its quoted title (the entry's, or the page's heading); one that names no page, such
as `None: <reason>` or a cross-reference in backticks, is left alone (a backtick-leading entry names a CORA source file first). `check-references.py`
renders the same line from the entry and flags every docstring entry that differs.

The stamps (`Reviewed:`, `Last update:`) are not touched: a bibliography line says nothing
about what a statement means.
"""

# Authors:       Claude Sonnet 5.5
# Written:       25-October-2026

import importlib.util
import re
import sys
import textwrap
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import refentry  # noqa: E402

spec = importlib.util.spec_from_file_location("check_references", HERE.parent / "check-references.py")
cr = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cr)

WIDTH = 100  # the line limit of `check-conventions.sh`
INDENT = " " * 6


def pages():
    """`{bare title: (rendering, page)}` over the titles of the pages' entries and headings."""
    out = {}
    for path in sorted(cr.REFS.glob(cr.PAPER_GLOB)):
        paper = cr.Paper(path, lambda m: None)
        if not paper.bib:
            continue
        line = (refentry.render(paper.bib), path)
        out.setdefault(refentry.tnorm(paper.bib["title"]), line)
        out.setdefault(refentry.tnorm(paper.title), line)
    return out


def wrap(number, line, lead=""):
    return textwrap.wrap(line, width=WIDTH, initial_indent=f"{lead}* [{number}] ",
                         subsequent_indent=lead + INDENT, break_long_words=False,
                         break_on_hyphens=False)


def rewrite(text, rendered, lean):
    """`text` with every entry that names a page replaced by a link to the page, its text the
    page's rendering; `lean` is the file, the link being relative to it."""
    m = re.search(r"^## References\s*$(.*?)(?=^-/)", text, re.S | re.M)
    if not m:
        return text
    lines = m.group(1).split("\n")
    out, i = [], 0
    while i < len(lines):
        e = cr.ENTRY.match(lines[i])
        if not e:
            out.append(lines[i])
            i += 1
            continue
        j = i + 1
        while j < len(lines) and lines[j].strip() and not cr.ENTRY.match(lines[j]):
            j += 1
        flat = cr.FLAT(" ".join([e.group(2)] + lines[i + 1:j]))
        title = refentry.quoted_title(flat)
        page = rendered.get(refentry.tnorm(title)) if title else None
        want = f"[{page[0]}]({cr.page_link(lean, page[1])})" if page else None
        if want is None or want == flat or flat.startswith("`"):
            out.extend(lines[i:j])
        else:
            lead = re.match(r"\s*", lines[i]).group(0)
            out.extend(wrap(e.group(1), want, lead))
        i = j
    return text[: m.start(1)] + "\n".join(out) + text[m.end(1):]


def main():
    check = "--check" in sys.argv[1:]
    rendered = pages()
    changed = 0
    for path in sorted(cr.SRC.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        new = rewrite(text, rendered, path)
        if new != text:
            changed += 1
            if check:
                print(path.relative_to(cr.ROOT).as_posix())
            else:
                path.write_text(new, encoding="utf-8")
    print(f"{changed} file(s) {'would change' if check else 'rewritten'}")
    return 1 if check and changed else 0


if __name__ == "__main__":
    sys.exit(main())
