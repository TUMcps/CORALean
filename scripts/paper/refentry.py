#!/usr/bin/env python3
"""The BibTeX entry of a `references/<year>/*.md` page, and what is made from it (#265).

Each page carries exactly one fenced `bibtex` block: the page's only bibliographic record.
Everything else is derived from it, here:

* `parse(text)` reads the block and `problems(entry)` says what is malformed;
* `render(entry)` is the one line every Lean module docstring writes under `## References`,
  `<authors>. "<Title>". <Venue>, <year>.`, authors as `A. Name, B. Name and C. Name`,
  the title and venue with the protecting braces of BibTeX dropped;
* `to_bibtex(entry)` is the entry as `appendix-errors.bib` prints it, accents as LaTeX commands.

Used by `check-references.py`, `errors-table.py` and `render-references.py`; not run on its own.
"""

# Authors:       Claude Sonnet 5.5
# Written:       25-October-2026

import re
import unicodedata

BLOCK = re.compile(r"^```bibtex\n(.*?)^```[ \t]*$", re.S | re.M)
HEAD = re.compile(r"^@(\w+)\{([A-Za-z0-9:_-]+),\s*$")
FIELD = re.compile(r"^  (\w+) = \{(.*)\},?$")
# What a page's entry may be, and the fields it needs; `publisher` only where the type requires
# it. No volume, pages, DOI, note or URL: the page's `**Source:**` line names the version read.
TYPES = {
    "article": ("author", "title", "journal", "year"),
    "inproceedings": ("author", "title", "booktitle", "year"),
    "incollection": ("author", "title", "booktitle", "publisher", "year"),
    # A manual or a specification: the venue is the body that publishes it.
    "manual": ("author", "title", "publisher", "year"),
}
ORDER = ("author", "title", "journal", "booktitle", "publisher", "year")
# `**In the paper's bibliography.**`: the key is an entry of the paper's own references.bib,
# so appendix-errors.bib does not define it.
PAPER_MARK = "**In the paper's bibliography.**"
NAME = re.compile(r"^[^,{}]+, \S.*$|^\{[^{}]+\}$")


def blocks(text):
    return BLOCK.findall(text)


def parse(text):
    """`{type, key, <field>...}` of the page's entry, or `None` unless it holds exactly one block
    that parses; `problems()` says what is wrong with the rest."""
    found = blocks(text)
    if len(found) != 1:
        return None
    lines = [l for l in found[0].splitlines() if l.strip()]
    head = HEAD.match(lines[0]) if lines else None
    if not head or lines[-1] != "}":
        return None
    entry = {"type": head.group(1), "key": head.group(2), "fields": []}
    for line in lines[1:-1]:
        m = FIELD.match(line)
        if not m:
            return None
        entry["fields"].append(m.group(1))
        entry[m.group(1)] = m.group(2)
    return entry


def problems(text):
    """What is wrong with the page's entry, as a list of sentences; empty when it is well-formed."""
    found = blocks(text)
    if len(found) != 1:
        return [f"has {len(found)} ```bibtex blocks; a page carries exactly one"]
    entry = parse(text)
    if entry is None:
        return ["the ```bibtex block is not `@type{key,` then `  field = {value},` lines and `}`"]
    out = []
    need = TYPES.get(entry["type"])
    if need is None:
        return [f"entry type `{entry['type']}` is none of {', '.join(sorted(TYPES))}"]
    if entry["fields"] != [f for f in ORDER if f in need]:
        out.append(f"the fields of a `{entry['type']}` are exactly "
                   f"{', '.join(f for f in ORDER if f in need)}, in that order; "
                   f"found {', '.join(entry['fields'])}")
    for f in need:
        v = entry.get(f, "")
        if not v.strip():
            # A venue the publication itself does not confirm is left blank, never guessed.
            if f not in ("journal", "booktitle"):
                out.append(f"field `{f}` is empty")
        elif v.count("{") != v.count("}") or "\n" in v:
            out.append(f"field `{f}` has unbalanced braces")
    if not re.fullmatch(r"\d{4}", entry.get("year", "")):
        out.append("`year` is four digits")
    for a in entry.get("author", "").split(" and "):
        if not NAME.match(a.strip()):
            out.append(f"author `{a}` is not `Last, F. M.`")
    return out


def unbrace(s):
    """The text of a field without BibTeX's protecting braces."""
    return re.sub(r"[{}]", "", s)


def authors_line(entry):
    names = []
    for a in entry["author"].split(" and "):
        a = a.strip()
        if "," in a and not a.startswith("{"):
            last, first = a.split(",", 1)
            a = f"{first.strip()} {last.strip()}"
        names.append(unbrace(a))
    return names[0] if len(names) == 1 else ", ".join(names[:-1]) + " and " + names[-1]


def venue(entry):
    if entry["type"] == "manual":
        return unbrace(entry.get("publisher", ""))
    return unbrace(entry.get("journal") or entry.get("booktitle") or "")


def render(entry):
    """The one docstring line: `<authors>. "<Title>". <Venue>, <year>.`"""
    v = venue(entry)
    return f'{authors_line(entry)}. "{unbrace(entry["title"])}". ' + (f"{v}, " if v else "") + f'{entry["year"]}.'


# --- the entry as appendix-errors.bib prints it ------------------------------------------- #

MARKS = {"̀": "`", "́": "'", "̂": "^", "̈": '"', "̃": "~",
         "̄": "=", "̇": ".", "̌": "v", "̆": "u", "̋": "H",
         "̧": "c", "̊": "r", "̨": "k"}
LETTERS = {"ı": "{\\i}", "ø": "{\\o}", "Ø": "{\\O}", "ß": "{\\ss}",
           "ł": "{\\l}", "Ł": "{\\L}", "æ": "{\\ae}", "Æ": "{\\AE}"}
PUNCT = {"–": "--", "—": "---", "−": "$-$", "’": "'", "‘": "`",
         "“": "``", "”": "''", " ": "~", "₋": "$_-$", "φ": "$\\varphi$"}


def latex(s):
    """A field in ASCII: accents as `{\\'e}`, dashes as `--`; braces already in `s` stay."""
    out = []
    for ch in s:
        if ch in LETTERS:
            out.append(LETTERS[ch])
        elif ch in PUNCT:
            out.append(PUNCT[ch])
        elif ord(ch) < 128:
            out.append(ch)
        else:
            base, *marks = unicodedata.normalize("NFD", ch)
            if len(marks) != 1 or marks[0] not in MARKS:
                raise ValueError(f"no LaTeX spelling for {ch!r} in {s!r}")
            cmd = MARKS[marks[0]]
            if cmd.isalpha():
                out.append("{\\" + cmd + "{" + base + "}}")
            else:
                out.append("{\\" + cmd + base + "}")
    return "".join(out)


def to_bibtex(entry):
    lines = [f"@{entry['type']}{{{entry['key']},"]
    fields = [f for f in ORDER if f in entry]
    for i, f in enumerate(fields):
        lines.append(f"  {f} = {{{latex(entry[f])}}}" + ("," if i < len(fields) - 1 else ""))
    lines.append("}")
    return "\n".join(lines)


# --- finding the page a docstring entry means ---------------------------------------------- #

def tnorm(s):
    """A title as a bare word string: no accents, case, braces or punctuation."""
    s = unicodedata.normalize("NFKD", unbrace(s))
    return re.sub(r"[^a-z0-9]+", " ", "".join(c for c in s if not unicodedata.combining(c)).lower()).strip()


def quoted_title(line):
    """The `"Title"` of a docstring entry, or `None`."""
    m = re.search(r'"(.+?)"', line)
    return m.group(1) if m else None
