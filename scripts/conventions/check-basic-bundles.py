#!/usr/bin/env python3
"""Checks the `Basic.lean` bundles (CONTRIBUTING, "Small declarations"; issue #137).

    python3 scripts/conventions/check-basic-bundles.py

A declaration of at most `MAX_CODE` code lines lives in a section of its directory's
`Basic.lean`, not in a file of its own. Called from `check-conventions.sh`, which handles the
header, the line lengths and every author block field; this adds what needs a parse of the
sections or the import graph:

* a `Basic.lean`: no file-level author block; its sections sit in *groups*, each under one
  context block (`groups`: `namespace`s, `open`s and `variable`s, the sections, the `end`s;
  a section holds no context line of its own, a block opens with `namespace` or `section`,
  closes with matching `end`s, has a section under it, and repeats no neighbour's lines; a
  namespace holding several `variable` sets stays open, each set in a nested `section` … `end`,
  and `end X` directly followed by `namespace X` is rejected);
  only blank lines between `BEGIN CODE`, the blocks, the sections and `END OF CODE`;
  each section opens with its banner, naming the declaration,
  with its own author block directly under it and one blank line under that; one declaration
  per section (`Complexity/` included: its `Operations/` and `Theorems/` are directories like any
  other), at most `MAX_CODE` code lines, a docstring on the (first) declaration, no
  `MAIN`/`AUXILIARY` marker, no CORA model or witness; sections in order within a group
  (`order_problems`: alphabetical, after the sections they use) and groups in order by their
  first section (`group_order_problems`);
* every other file: one that is eligible (`eligible`: its module docstring, moved into the
  declaration's own as `section_doc` moves it, still within the cap) is in a `Basic.lean`,
  unless moving it there would close an import cycle (`closes_cycle`: a path from the file to
  `Basic.lean`, or back, through a third module). No list: the cycle is the whole exception.

Code lines are counted as issue #137 defines them: the non-blank, non-comment lines between the
code markers, declaration docstrings included; `namespace`, `section`, `end`, `open`,
`variable` and `universe` lines are context (the group's, not the section's) and do not count.

The parsing is the shallow kind `check-conventions.sh` does: comments stripped by a
two-character scanner, commands matched at the start of a line. `scripts/review.py` and
`scripts/tools/author-blocks.py` read sections through `sections()` here.
"""
import heapq
import importlib.util
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
SRC = ROOT / "src"
# The CORA-bug appendix links the counterexample and the fix of each bug by file; those files
# keep their own (see `scripts/paper/cora-bugs-table.py`, which writes it from `cora-bugs.json`).
CORA_BUGS_TEX = ROOT / "experiments" / "paper" / "latex" / "appendix-cora-bugs.tex"

MAX_CODE = 5
BASIC = "Basic.lean"


def set_root(root):
    """Point every path above at another checkout (the conversion runs on an archive)."""
    global ROOT, SRC, CORA_BUGS_TEX, _BUGS
    ROOT = Path(root).resolve()
    SRC = ROOT / "src"
    CORA_BUGS_TEX = ROOT / "experiments" / "paper" / "latex" / "appendix-cora-bugs.tex"
    _BUGS = None

BEGIN = "-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --"
END = "-- ---------------------------------------  END OF CODE  ---------------------------------------- --"
AUTHOR_FIELDS = ("-- Authors:", "-- Written:", "-- Last update:", "-- Reviewed:")
REVIEW_CONT = re.compile(r"^--" + " " * 16 + r"\d")

KIND = r"(def|theorem|lemma|abbrev|instance|structure|inductive|class|opaque|example)"
MODS = r"((private|protected|noncomputable|partial|scoped|unsafe|nonrec)\s+)*"
DECL = re.compile(r"^(@\[[^\]]*\]\s*)?" + MODS + KIND + r"(\s|$)")
# What may precede a declaration on lines of its own and belongs to it.
PREFIX = re.compile(r"^(@\[[^\]]*\]\s*$|(set_option|open|omit|include)\b.*\bin\s*$)")
# What continues a declaration at column 0.
CONTINUES = re.compile(r"^(termination_by|decreasing_by|deriving|where|\|)(\s|$)")
# Context: scoping, not code, and not counted.
CONTEXT = re.compile(r"^(namespace|section|end|open|variable|universe)(\s|$)")
# Allowed beside the declaration, and counted: a local instance, an `omit`/`include`.
LOCAL = re.compile(r"^(attribute\s+\[local instance\]|omit|include)(\s|$)")
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(\S+)", re.M)
SECTION_BANNER = re.compile(r"^-- =+  `([^`]+)`  =+ --$")
MARKER = re.compile(r"^-- [-=]")
WITNESS = re.compile(r"Cora|Counterexample")
# A Lean identifier, dotted names whole: letters (Greek and letter-like included), then
# letters, digits, `_'!?` and subscripts; never a superscript (`E.shape⁻¹`, `Gᵀ`).
_LETTER = r"A-Za-z_\u00C0-\u024F\u0370-\u03FF\u2100-\u214F\U0001D400-\U0001D7FF"
_SUB = r"\u2080-\u209C\u1D62-\u1D6A\u2C7C"
IDENT = re.compile(rf"[{_LETTER}][{_LETTER}0-9'!?{_SUB}.]*")


def charlen(s):
    return len(s)


def banner(label):
    """The 100-character banner of a section, `=` fill split as the `MAIN ...` markers split it."""
    inner = 90 - charlen(label)
    left, right = inner // 2, inner - inner // 2
    return f"-- {'=' * left}  {label}  {'=' * right} --"


COMMENT_TOKEN = re.compile(r"--|/-|-/")


def scan(lines):
    """Per line: (code outside comments, comment depth at its start, touches a docstring)."""
    depth, kind, out = 0, None, []
    for line in lines:
        if depth == 0 and "-" not in line:
            out.append((line, 0, False))
            continue
        start, code, pos = depth, [], 0
        doc = depth > 0 and kind == "doc"
        for m in COMMENT_TOKEN.finditer(line):
            tok, i = m.group(), m.start()
            if i < pos:
                continue
            if depth == 0 and tok == "--":
                code.append(line[pos:i])
                pos = len(line)
                break
            if tok == "/-":
                if depth == 0:
                    code.append(line[pos:i])
                    nxt = line[i + 2:i + 3]
                    kind = "doc" if nxt == "-" else ("mod" if nxt == "!" else "blk")
                    doc = doc or kind == "doc"
                depth += 1
                pos = i + 2
            elif tok == "-/" and depth:
                depth -= 1
                pos = i + 2
            elif tok == "-/" or tok == "--":
                continue
        if depth == 0 and pos < len(line):
            code.append(line[pos:])
        out.append(("".join(code), start, doc))
    return out


def decl_name(code):
    """The name a declaration line declares, as written; `""` for an anonymous instance."""
    m = DECL.match(code)
    rest = code[m.end(4):].strip()
    rest = re.sub(r"^\(priority\s*:=\s*\w+\)\s*", "", rest)
    return re.split(r"[\s:({\[]", rest)[0] if rest else ""


class Item:
    """One top-level command of a code region: `decl`, `context`, `local` or `other`."""

    def __init__(self, kind, start, word=""):
        self.kind, self.start, self.end, self.word = kind, start, start, word
        self.decl_kind, self.name = "", ""


def items(lines, sc, lo, hi):
    """The top-level commands of lines `lo..hi-1` (markers skipped)."""
    out, cur = [], None
    for i in range(lo, hi):
        raw = lines[i]
        code, depth, _ = sc[i]
        if MARKER.match(raw) or SECTION_BANNER.match(raw):
            continue
        top = depth == 0 and raw[:1] not in ("", " ", "\t") and not raw.startswith("--")
        if not top:
            if cur is not None and raw.strip() and not raw.lstrip().startswith("--"):
                cur.end = i
            continue
        if raw.startswith("/--"):
            if cur is None or cur.kind != "pre":
                cur = Item("pre", i)
                out.append(cur)
            cur.end = i
        elif raw.startswith("/-"):
            continue
        elif DECL.match(code):
            if cur is None or cur.kind != "pre":
                cur = Item("decl", i)
                out.append(cur)
            cur.kind, cur.end = "decl", i
            cur.decl_kind = DECL.match(code).group(4)
            cur.name = decl_name(code)
        elif PREFIX.match(code.rstrip()):
            if cur is None or cur.kind != "pre":
                cur = Item("pre", i)
                out.append(cur)
            cur.end = i
        elif CONTINUES.match(code) and cur is not None and cur.kind == "decl":
            cur.end = i
        elif LOCAL.match(code):
            cur = Item("local", i, code.split()[0])
            out.append(cur)
        elif CONTEXT.match(code):
            cur = Item("context", i, code.split()[0])
            out.append(cur)
        else:
            cur = Item("other", i, (code.split() or [raw])[0])
            out.append(cur)
    return out


def count_code(lines, sc, its, lo, hi):
    """Code lines of `lo..hi-1`, as issue #137 counts them."""
    context = set()
    for it in its:
        if it.kind == "context":
            context.update(range(it.start, it.end + 1))
    n = 0
    for i in range(lo, hi):
        raw = lines[i]
        code, _, doc = sc[i]
        if not raw.strip() or MARKER.match(raw) or i in context:
            continue
        if code.strip() or doc:
            n += 1
    return n


class Region:
    """A run of code: a whole file's, or one section's."""

    def __init__(self, lines, sc, lo, hi):
        self.lo, self.hi = lo, hi
        self.items = items(lines, sc, lo, hi)
        self.code = count_code(lines, sc, self.items, lo, hi)
        self.decls = [it for it in self.items if it.kind == "decl"]
        self.others = [it for it in self.items if it.kind in ("other", "pre")]

    def tokens(self, sc):
        """The identifiers of the region's code, dotted names whole; comments and docstrings
        left out."""
        toks = set()
        for i in range(self.lo, self.hi):
            toks.update(IDENT.findall(sc[i][0]))
        return toks


class LeanFile:
    def __init__(self, path, text=None):
        self.path = Path(path)
        self.rel = self.path.relative_to(ROOT).as_posix()
        self.text = self.path.read_text(encoding="utf-8") if text is None else text
        self.lines = self.text.split("\n")
        self.sc = scan(self.lines)
        self.imports = IMPORT.findall(self.text)
        self.begin = self.lines.index(BEGIN) if BEGIN in self.lines else -1
        self.end = self.lines.index(END) if END in self.lines else -1
        self.region = (Region(self.lines, self.sc, self.begin + 1, self.end)
                       if 0 <= self.begin < self.end else None)

    @property
    def module_doc(self):
        """The module docstring's lines."""
        for i, (_, depth, _) in enumerate(self.sc):
            if depth == 0 and self.lines[i].startswith("/-!"):
                j = i
                while j < len(self.lines) and "-/" not in self.lines[j]:
                    j += 1
                return self.lines[i:j + 1]
        return []

    def single(self):
        """Whether the code region is one declaration."""
        r = self.region
        if r is None or r.others or not r.decls:
            return False
        return len(r.decls) == 1


def module_of(rel):
    return rel[len("src/"):-len(".lean")].replace("/", ".")


def path_of(mod):
    return "src/" + mod.replace(".", "/") + ".lean"


def class_root(d):
    return any((d / x).is_dir() for x in ("Operations", "Theorems", "Definitions"))


_BUGS = None


def cora_bug_files():
    global _BUGS
    if _BUGS is None:
        text = CORA_BUGS_TEX.read_text(encoding="utf-8") if CORA_BUGS_TEX.exists() else ""
        _BUGS = set(re.findall(r"coraleanrepo(?:/| )([^}]*\.lean)", text))
    return _BUGS


def excluded(lf):
    """Why a file keeps its own file whatever its size, or `None`."""
    rel, p = lf.rel, lf.path
    if rel.startswith("src/CORALean/Examples/"):
        return "Examples/"
    if p.name in ("API.lean", "Instances.lean", BASIC) or rel == "src/CORALean.lean":
        return p.name
    if p.stem in (p.parent.name, p.parent.parent.name) or class_root(p.parent):
        return "main-type file"
    if "Counterexamples" in Path(rel).parts:
        return "refutation or CORA model (Counterexamples/)"
    if WITNESS.search(p.stem):
        return "CORA model the library imports (COUNTEREXAMPLE_EXCEPTIONS)"
    if rel in cora_bug_files():
        return "linked from the CORA-bug appendix"
    if any(l.startswith("## References") for l in lf.module_doc):
        return "cites a paper"
    if ("Float" in p.stem and "Float" not in Path(rel).parts[:-1] and lf.region is not None
            and not any("Float" in d.name for d in lf.region.decls)):
        # `check-references.py` and the paper's statistics read the float layer off a file
        # name, a directory or a declaration name; in `Basic.lean` only the last would remain.
        return "float layer named by its file alone"
    return None


MAX_DECL_DOC = 3  # lines of a declaration docstring, as in `check-conventions.sh`
MAX_LINE = 100
DOC_PREFIX = re.compile(r"^(set_option|open|omit|include)\b.*\bin\s*$")


def norm(s):
    return " ".join(s.split())


def first_doc(lf):
    """`(start, stop, text lines)` of the first declaration's docstring (stop one past its
    last line), or `(insert at, insert at, None)` where one would go: under any
    `set_option … in` heading the declaration, above its attributes."""
    L = lf.lines
    d = lf.region.decls[0]
    i = d.start
    while i < len(L) and DOC_PREFIX.match(L[i]):
        i += 1
    if L[i].startswith("/--"):
        j = i
        while "-/" not in L[j]:
            j += 1
        text = "\n".join(L[i:j + 1])
        text = text[len("/--"):text.rindex("-/")]
        return i, j + 1, [l.rstrip() for l in text.strip().split("\n")]
    return i, i, None


def module_prose(lf):
    """`(title, paragraphs)` of the module docstring: the `# ` title line's text, and the rest
    as paragraphs of lines."""
    doc = lf.module_doc
    if not doc:
        return "", []
    body = "\n".join(doc)
    body = body[body.index("/-!") + 3:body.rindex("-/")]
    lines = body.split("\n")
    title = ""
    while lines and not lines[0].strip():
        lines.pop(0)
    if lines and lines[0].lstrip().startswith("# "):
        title = lines.pop(0).lstrip()[2:].strip()
    paras, cur = [], []
    for l in lines + [""]:
        if l.startswith("## Inputs"):
            break  # the inputs/outputs sections (#251) are a file's, not prose a section takes over
        if l.strip():
            cur.append(l.rstrip())
        elif cur:
            paras.append(cur)
            cur = []
    return title, paras


def section_doc(lf):
    """`(kind, docstring lines)` the declaration carries in its section: the module
    docstring's content moves there, since a section has no module docstring of its own.
    `moved`: the declaration had none, and the module docstring less its title becomes it
    (only the title, when that is all there is); `merged`: the paragraphs of the module
    docstring the declaration's own does not already say are appended; `kept`: nothing to
    add."""
    _, _, old = first_doc(lf)
    title, paras = module_prose(lf)
    if old is None:
        text = [l for k, p in enumerate(paras) for l in ([""] if k else []) + p]
        kind = "moved"
        if not text:
            text, kind = ([title] if title else []), "title"
    else:
        have = norm(" ".join(old))
        extra = [p for p in paras if norm(" ".join(p)) not in have]
        text = old + [l for p in extra for l in [""] + p]
        kind = "merged" if extra else "kept"
    if not text:
        return kind, None
    if len(text) == 1:
        return kind, [f"/-- {text[0]} -/"]
    return kind, [f"/-- {text[0]}"] + text[1:-1] + [f"{text[-1]} -/"]


def bundled_code(lf):
    """The code lines of the declaration's section, its moved docstring counted."""
    s, e, _ = first_doc(lf)
    _, doc = section_doc(lf)
    return lf.region.code - sum(1 for l in lf.lines[s:e] if l.strip()) + \
        sum(1 for l in (doc or []) if l.strip())


def fits(lf):
    """Whether the declaration, its module docstring moved into its own, stays within the
    section cap and the docstring limits (three lines, a hundred characters each)."""
    _, doc = section_doc(lf)
    return (bundled_code(lf) <= MAX_CODE and doc is not None and len(doc) <= MAX_DECL_DOC
            and all(len(l) <= MAX_LINE for l in doc))


def eligible(lf):
    """Whether a file's declaration belongs in its directory's `Basic.lean`."""
    return (lf.single() and lf.region.code <= MAX_CODE and excluded(lf) is None and fits(lf))


class Section:
    def __init__(self, bf, start, stop):
        lines = bf.lines
        self.file, self.start, self.stop = bf, start, stop  # banner line, one past the last
        m = SECTION_BANNER.match(lines[start])
        self.label = m.group(1) if m else ""
        self.banner_ok = m is not None and lines[start] == banner(f"`{self.label}`")
        a = start + 1
        self.author = a if a < stop and lines[a].startswith("-- Authors:") else -1
        j = a
        if self.author >= 0:
            j = a + 4
            while j < stop and REVIEW_CONT.match(lines[j]):
                j += 1
        self.block_end = j  # one past the author block
        lo = j
        while lo < stop and not lines[lo].strip():
            lo += 1
        self.blank_after = lo - j
        hi = stop
        while hi > lo and not lines[hi - 1].strip():
            hi -= 1
        self.body_lo, self.body_hi = lo, hi
        self.region = Region(lines, bf.sc, lo, hi)
        self.names = [d.name for d in self.region.decls]
        self.group = None

    @property
    def qualified(self):
        """The first declaration's name with the namespaces of its block, below `CORALean`."""
        if not self.names:
            return ""
        full = ".".join(self.group.namespaces + [self.names[0]]) if self.group else self.names[0]
        return full[len("CORALean."):] if full.startswith("CORALean.") else full

    def label_ok(self):
        """A banner names the declaration as written, or — where two sections of one bundle
        would otherwise share a banner — qualified by its namespace below `CORALean`."""
        return bool(self.names) and self.label in (self.names[0], self.qualified)

    @property
    def key(self):
        return (self.label.casefold(), self.label)


def sections(lf):
    """The sections of a `Basic.lean`, in file order. A section runs from its banner to the next
    banner or the next context line (`namespace`, `open`, `variable`, `end` …) at column 0:
    context belongs to a group (`groups`), not to a section."""
    lines = lf.lines
    if lf.begin < 0 or lf.end < 0:
        return []
    starts = [i for i in range(lf.begin + 1, lf.end) if SECTION_BANNER.match(lines[i])]
    ctx = [it.start for it in lf.region.items if it.kind == "context"]
    out = []
    for k, s in enumerate(starts):
        stop = starts[k + 1] if k + 1 < len(starts) else lf.end
        stop = min([stop] + [c for c in ctx if c > s])
        out.append(Section(lf, s, stop))
    return out


class Group:
    """A run of sections under one context block: the `namespace`/`open`/`variable` lines above
    them and the `end` lines below. Sections that sit outside any block form a group of their
    own with no context lines. A namespace holding several `variable` sets is a *frame*: the
    `namespace` lines once, then one `section` ... `end` block per set; each such block is a
    group, the later ones carrying the frame's `namespace` lines as `inherited`."""

    def __init__(self, start, rootless=False):
        self.start = start
        self.context = []        # [(line index, text)] of the opening block
        self.inherited = []      # [(line index, text)]: the `namespace` lines of the frame it sits in
        self.sections = []
        self.stack = []          # the names `end` must close, innermost last
        self.rootless = rootless
        self.phase = "sections" if rootless else "open"   # open, sections, closing, done

    @property
    def label(self):
        return self.sections[0].label if self.sections else ""

    @property
    def namespaces(self):
        return [t.split()[1] for _, t in self.inherited + self.context
                if t.startswith("namespace ")]

    def signature(self):
        return tuple(" ".join(t.split()) for _, t in self.inherited + self.context)


def groups(lf, secs, say):
    """The groups of a `Basic.lean`, in file order: each section under the context block it is
    wrapped in. A malformed block is reported through `say(line index, message)`.

    A namespace opened once may hold several `section` blocks, one per set of `variable`s: the
    first of them is the group that opened the namespace, the next ones are groups of their own
    with the namespace as their frame (`Group.inherited`). A namespace closed and reopened at
    once — `end X` directly followed by `namespace X` — is what a frame replaces; it is
    reported."""
    lines = lf.lines
    events = [(it.start, "ctx", it) for it in lf.region.items if it.kind == "context"]
    events += [(s.start, "sec", s) for s in secs]
    events.sort(key=lambda e: e[0])
    out, cur = [], None
    frame = None                 # [namespace lines of the open frame, names `end` must close]
    last_end = None              # the name the latest context event closed, with no section since
    for i, kind, x in events:
        if kind == "ctx":
            text = " ".join(l.strip() for l in lines[x.start:x.end + 1])
            if x.word == "end":
                owner = cur if cur is not None and not cur.rootless and cur.stack else None
                if owner is None and frame is not None and frame[1]:
                    want = frame[1].pop()
                    if text.split()[1:2] != [want]:
                        say(i, f"`{text}` closes `namespace {want}`")
                    last_end = want
                    if not frame[1]:
                        frame = None
                    continue
                if owner is None:
                    say(i, "`end` with no `namespace` or `section` open")
                    continue
                want = owner.stack.pop()
                if want is not None and text.split()[1:2] != [want]:
                    say(i, f"`{text}` closes `namespace {want}`")
                last_end = want
                owner.phase = "closing" if owner.stack else "done"
                continue
            if (x.word == "section" and cur is not None and not cur.rootless
                    and cur.phase == "closing" and cur.stack
                    and all(w is not None for w in cur.stack)):
                # the namespace stays open: the block just closed was a section of its frame
                frame = [[(j, t) for j, t in cur.context if t.startswith("namespace ")],
                         list(cur.stack)]
                cur.stack = []
                cur.phase = "done"
                cur = Group(i)
                cur.inherited = list(frame[0])
                out.append(cur)
                cur.context.append((i, text))
                cur.stack.append(None)
                last_end = None
                continue
            if cur is None or cur.rootless or cur.phase == "done":
                cur = Group(i)
                out.append(cur)
                if frame is not None and x.word == "section":
                    cur.inherited = list(frame[0])
                elif x.word == "namespace" and last_end is not None:
                    name = text.split()[1] if len(text.split()) > 1 else None
                    if name == last_end:
                        say(i, f"`end {last_end}` directly followed by `namespace {name}`: the"
                               " namespace stays open, each set of `variable`s in a nested"
                               " `section` … `end`")
            elif cur.phase != "open":
                say(i, "context after the sections of a block — close it with `end` first; a"
                       " section holds no `namespace`, `open` or `variable` of its own")
                continue
            if not cur.context and x.word not in ("namespace", "section"):
                say(i, f"a context block opens with `namespace` or `section`, not `{x.word}`:"
                       " an `open` or `variable` outside one leaks into every section after it")
            cur.context.append((i, text))
            last_end = None
            if x.word in ("namespace", "section"):
                cur.stack.append(text.split()[1] if len(text.split()) > 1 else None)
        else:
            last_end = None
            if cur is None or cur.phase == "done":
                cur = Group(i, rootless=True)
                out.append(cur)
            elif cur.phase == "closing":
                say(i, "a section between the `end` lines of a block")
            elif cur.phase == "open":
                cur.phase = "sections"
            cur.sections.append(x)
            x.group = cur
    if frame is not None:
        say(frame[0][0][0] if frame[0] else 0, "a namespace is never closed: it needs an `end`")
    for g in out:
        if g.stack:
            say(g.start, "a context block is never closed: it needs an `end` for every"
                         " `namespace` and `section`")
        if not g.sections:
            say(g.start, "a context block with no section under it")
    return out


def relations(secs):
    """`(certain, possible)`, each `{label: {labels it uses}}`.

    A section *certainly* uses another whose declaration it names in full, as written
    (`Interval.center`, or ending in it, `Real.Interval.center`). It *possibly* uses one whose
    declaration's last component is a component of any of its identifiers (`I.center`,
    `center`): dot notation and an open namespace make that the most text can say, and it
    over-approximates (`Real.cosh` possibly uses `Interval.cosh`). A section naming one of its own
    declarations uses nothing by it, so the two layers' `MatExp.corrTerm` do not use each other.
    """
    full, last = {}, {}
    for s in secs:
        for n in s.names:
            if n:
                full.setdefault(n, set()).add(s.label)
                last.setdefault(n.split(".")[-1], set()).add(s.label)
    certain, possible = {}, {}
    for s in secs:
        own = set(s.names)
        toks = s.region.tokens(s.file.sc)
        c, p = set(), set()
        for t in toks:
            parts = t.split(".")
            tails = {".".join(parts[k:]) for k in range(len(parts))}
            if tails & own:
                continue
            for tail in tails:
                c |= full.get(tail, set())
            for part in parts:
                p |= last.get(part, set())
        certain[s.label] = c - {s.label}
        possible[s.label] = (p | c) - {s.label}
    return certain, possible


def canonical_order(labels, deps):
    """Alphabetical, except that a section comes after every section it uses (alphabetical
    among the ones free to go next). `None` if the uses go round in a circle."""
    key = lambda l: (l.casefold(), l)
    indeg = {l: 0 for l in labels}
    users = {l: set() for l in labels}
    for l in labels:
        for d in deps.get(l, ()):
            if d in indeg:
                indeg[l] += 1
                users[d].add(l)
    heap = [(key(l), l) for l in labels if indeg[l] == 0]
    heapq.heapify(heap)
    out = []
    while heap:
        _, l = heapq.heappop(heap)
        out.append(l)
        for u in users[l]:
            indeg[u] -= 1
            if indeg[u] == 0:
                heapq.heappush(heap, (key(u), u))
    return out if len(out) == len(labels) else None


def order_check(labels, certain, possible):
    """`[(index, message)]` where `labels` is not in the canonical order: a unit placed before a
    unit it certainly uses, or after an alphabetically smaller one that nothing kept waiting —
    at its place, every unit still to come and alphabetically before it must possibly use one at
    or after that place, or it would have come first."""
    pos = {l: i for i, l in enumerate(labels)}
    key = lambda l: (l.casefold(), l)
    out = []
    for i, l in enumerate(labels):
        late = sorted(d for d in certain[l] if pos[d] > i)
        if late:
            out.append((i, f"`{l}` uses {', '.join('`' + d + '`' for d in late)},"
                           f" which {'come' if len(late) > 1 else 'comes'} after it — a section follows"
                           " the sections it uses"))
        for t in labels[i + 1:]:
            if key(t) < key(l) and not any(i <= pos[d] < pos[t] for d in possible[t]):
                out.append((i, f"`{l}` comes before `{t}`, which uses nothing in between —"
                               " sections are alphabetical, after the sections they use"))
                break
    return out


def order_problems(secs):
    """`[(section, message)]` for the order of the sections of one group."""
    certain, possible = relations(secs)
    return [(secs[i], f"section {m}") for i, m in order_check([s.label for s in secs], certain, possible)]


def group_order_problems(secs, grps):
    """`[(group, message)]` for the order of the groups: by the label of the first section,
    after the groups whose sections they use, by the same rule as the sections of a group."""
    grps = [g for g in grps if g.sections]
    certain, possible = relations(secs)
    owner = {s.label: g.label for g in grps for s in g.sections}
    c = {g.label: set() for g in grps}
    p = {g.label: set() for g in grps}
    for g in grps:
        for s in g.sections:
            c[g.label] |= {owner[d] for d in certain[s.label]}
            p[g.label] |= {owner[d] for d in possible[s.label]}
        c[g.label].discard(g.label)
        p[g.label].discard(g.label)
    return [(grps[i], f"the block of {m}")
            for i, m in order_check([g.label for g in grps], c, p)]


def all_files():
    return sorted(SRC.rglob("*.lean"))


def import_graph(files):
    return {module_of(lf.rel): [m for m in lf.imports] for lf in files}


def tree_import_graph():
    """The import graph of every file under `src/`, read from the imports alone."""
    return {module_of(p.relative_to(ROOT).as_posix()): IMPORT.findall(p.read_text(encoding="utf-8"))
            for p in all_files()}


def closes_cycle(graph, a, b):
    """Whether merging modules `a` and `b` closes an import cycle: a path from one of them to
    one of them through some third module."""
    pair = {a, b}
    stack = [d for m in pair for d in graph.get(m, ()) if d not in pair]
    seen = set(stack)
    while stack:
        x = stack.pop()
        for d in graph.get(x, ()):
            if d in pair:
                return True
            if d not in seen:
                seen.add(d)
                stack.append(d)
    return False


def check_basic(lf, say):
    rel, lines = lf.rel, lf.lines
    where = lambda i: f"{rel}:{i + 1}"
    if rel.startswith("src/CORALean/Examples/"):
        say(f"{rel}:1: a `Basic.lean` is a module, outside `Examples/`")
    if lf.begin < 0 or lf.end < 0:
        say(f"{rel}:1: a `Basic.lean` frames its sections with `BEGIN CODE` and `END OF CODE`")
        return
    doc_end = max((i for i in range(lf.begin) if lines[i].rstrip().endswith("-/")), default=-1)
    for i in range(doc_end + 1, lf.begin):
        if lines[i].strip():
            say(f"{where(i)}: a `Basic.lean` has no file-level author block — each section carries"
                " its own, under its banner")
            break
    secs = sections(lf)
    if not secs:
        say(f"{rel}:1: a `Basic.lean` with no sections — delete it")
        return
    grps = groups(lf, secs, lambda i, msg: say(f"{where(i)}: {msg}"))
    first = min(g.start for g in grps)
    for i in range(lf.begin + 1, first):
        if lines[i].strip() and not MARKER.match(lines[i]):
            say(f"{where(i)}: nothing sits between `BEGIN CODE` and the first context block or"
                " section banner")
            break
    inside = set()
    for s in secs:
        inside.update(range(s.start, s.stop))
    for it in lf.region.items:
        if it.kind != "context" and it.start not in inside:
            say(f"{where(it.start)}: a declaration outside any section — every declaration is"
                " a section, under its banner")
    for a, b in zip(grps, grps[1:]):
        if a.context and a.signature() == b.signature():
            say(f"{where(b.start)}: this block repeats the one at line {a.start + 1} — the two"
                " groups are one, with their sections ordered together")
    seen = {}
    for s in secs:
        tag = where(s.start)
        if not s.banner_ok:
            say(f"{tag}: the section banner reads `{banner('`' + s.label + '`')}`, 100 characters")
        if s.label in seen:
            say(f"{tag}: a second section `{s.label}` (first at line {seen[s.label] + 1})")
        seen.setdefault(s.label, s.start)
        if s.author < 0:
            say(f"{tag}: the section's author block goes directly under its banner")
            continue
        for k, f in enumerate(AUTHOR_FIELDS):
            if not lines[s.author + k].startswith(f):
                say(f"{where(s.author + k)}: the section's author block reads `{f}` here")
        if s.blank_after != 1:
            say(f"{where(s.block_end)}: one blank line between a section's author block and its"
                f" code, not {s.blank_after}")
        for i in range(s.body_lo, s.body_hi):
            if MARKER.match(lines[i]):
                say(f"{where(i)}: a section carries no `MAIN`/`AUXILIARY` marker — its banner"
                    " names the declaration")
        r = s.region
        if r.others:
            say(f"{where(r.others[0].start)}: a section holds one declaration and its context,"
                f" not `{r.others[0].word or 'a docstring with no declaration'}`")
        if not r.decls:
            say(f"{tag}: section `{s.label}` declares nothing")
            continue
        if len(r.decls) > 1:
            say(f"{tag}: section `{s.label}` declares {len(r.decls)} things — one declaration per"
                " section")
        if not s.label_ok():
            say(f"{tag}: the banner names `{s.label}`, the section declares `{r.decls[0].name}`")
        elif s.label != s.names[0] and sum(t.names[:1] == s.names[:1] for t in secs) < 2:
            say(f"{tag}: the banner names `{s.label}` — qualified only where two sections share"
                f" `{s.names[0]}`")
        k = r.decls[0].start
        while k < s.body_hi and DOC_PREFIX.match(lines[k]):
            k += 1
        if not lines[k].startswith("/--"):
            say(f"{where(r.decls[0].start)}: `{s.label}` carries no docstring — in a section the"
                " declaration's `/-- … -/` is its description, there being no module docstring")
        if r.code > MAX_CODE:
            say(f"{tag}: section `{s.label}` is {r.code} code lines, over {MAX_CODE} — move it"
                " into a file of its own")
        if WITNESS.search(s.label.split(".")[-1]):
            say(f"{tag}: `{s.label}` is a CORA model or witness, which belongs in a `Counterexamples/` folder")
    for g in grps:
        for s, msg in order_problems(g.sections):
            say(f"{where(s.start)}: {msg}")
    for g, msg in group_order_problems(secs, grps):
        say(f"{where(g.sections[0].start)}: {msg}")


def main(argv=()):
    """Every check, or with `--files LIST --stage DIR` the per-file ones on the files LIST names
    (repository paths, one per line), their text read from `DIR/<path>`: what `check-conventions.sh
    --staged` runs on the index versions of a commit's files. A listed file is read where it
    stands in the repository for everything but its text (the directories the exclusions look at),
    and the rules that read other files stay out (the cycle test of a small file reads the import
    graph of the tree, its imports only). The hook sends a commit that touches an import down the
    full path."""
    msgs = []
    say = msgs.append
    if argv:
        if len(argv) != 4 or argv[0] != "--files" or argv[2] != "--stage":
            print("usage: check-basic-bundles.py [--files LIST --stage DIR]", file=sys.stderr)
            return 2
        stage = Path(argv[3])
        rels = [l.strip() for l in Path(argv[1]).read_text(encoding="utf-8").splitlines()
                if l.strip().endswith(".lean")]
        files = [LeanFile(ROOT / r, (stage / r).read_text(encoding="utf-8")) for r in rels]
        scoped = True
    else:
        files = [LeanFile(p) for p in all_files()]
        scoped = False
    by_rel = {lf.rel: lf for lf in files}
    graph = None if scoped else import_graph(files)
    for lf in files:
        if lf.path.name == BASIC:
            check_basic(lf, say)
    for lf in files:
        if lf.path.name == BASIC or not eligible(lf):
            continue
        if graph is None:
            graph = tree_import_graph()
        basic = (lf.path.parent / BASIC).relative_to(ROOT).as_posix()
        if closes_cycle(graph, module_of(lf.rel), module_of(basic)):
            continue
        say(f"{lf.rel}:1: one declaration of {lf.region.code} code lines, at most {MAX_CODE} —"
            f" it is a section of `{basic}` (CONTRIBUTING, \"Small declarations\"), unless moving"
            " it there would close an import cycle, and it closes none")
    for m in sorted(msgs):
        print(m)
    return 1 if msgs else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
