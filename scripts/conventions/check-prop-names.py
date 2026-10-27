#!/usr/bin/env python3
"""A `Prop`-valued definition is named so that `X.Name args` reads as a statement (#196, #257).

Every `def`, `abbrev`, `structure`, `inductive` and `class` under `src/` whose type is a `Prop`
(`: Prop`, `… → Prop`, `structure … : Prop where`) has a last name component of one of three forms:

* `Is…` or `Has…` (`IsCompact`, `HasDerivAt`, `IsTrajectory`), also lower-case (`isBounded`, `hasDeriv`);
* a *verb relation*: its first word, read up to the next capital letter, digit or `_`, is an English
  third-person verb: at least four letters, ending in `s`, but not in `ss`, `us` or `is`
  (`Encloses`, `Holds`, `HoldsOn`, `Covers`, `Satisfies`, `Represents`, `Reaches`, `containsPoint`).
  A noun or an adjective (`Sorted`, `Branch`, `Exact`) has no such first word and fails;
* a CORA mirror: a lower-case name that starts with the name of a CORA method of
  `references/coverage/cora-inventory.json`, the method's own spelling being the point
  (`eq`, `le`, `isequal`, `representsa_point`, `constrSat`).

There is no list of exceptions to these three forms. Two further rules keep the enclosure
predicates apart from the correctness bundles (#165):

* a Prop-valued definition with `Sound` in its name is a correctness bundle of an algorithm or a
  translation, and sits under `Specification/` or `LinearSys/Definitions/`;
  that a stored or abstract object over-approximates an exact function or set is `Encloses`;
* the first explicit argument of an `X.Encloses` is the enclosing object, of type `X` (so that
  `x.Encloses f` reads "x encloses f"), then the exact function or set, then any domain. Only an
  argument that the type of `x` depends on (`sys` in `OutputFloatModel … sys.q`) may come before
  it. The rule
  applies when `X` names a type (a `structure`, `inductive`, `class`, or a `def` or `abbrev` whose
  value is a type); a namespace that is no type, such as `ReachSequence`, has no object to put first.

Prints findings and exits 1 on any.

`--root DIR` reads another tree (used to test the rule on a mutated copy); `--survey` prints
every Prop-valued declaration as `path:line: name` and exits 0.
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
args = sys.argv[1:]
survey = "--survey" in args
if "--root" in args:
    ROOT = Path(args[args.index("--root") + 1]).resolve()
INVENTORY = ROOT / "references/coverage/cora-inventory.json"

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
    r"(def|abbrev|structure|inductive|class inductive|class)\s+([^\s({\[:]+)"
)


def strip_comment(l):
    return re.sub(r"\s--.*$", "", l)


def prop_decls(path):
    lines = path.read_text(encoding="utf-8").splitlines()
    inblock = False
    out = []
    for i, raw in enumerate(lines):
        if inblock:
            if "-/" in raw:
                inblock = False
            continue
        if raw.lstrip().startswith("/-") and "-/" not in raw:
            inblock = True
            continue
        m = DECL.match(raw)
        if not m:
            continue
        kind, name = m.group(1), m.group(2)
        if name.split(".")[-1].startswith("aux_") or re.match(r"^(?:@\[[^\]]*\]\s*)*private\s", raw):
            continue  # a helper of its own file, not part of the vocabulary
        head = []
        j = i
        while j < len(lines):
            l = strip_comment(lines[j])
            if j > i and (re.match(r"^\s*\|", l) or re.match(r"^(def|theorem|lemma|instance|structure|class|inductive|abbrev|namespace|section|end|open|@\[|/-)", l)):
                break
            head.append(l)
            k = l.find(":=")
            if k >= 0:
                head[-1] = l[:k]
                break
            if l.rstrip().endswith("where"):
                head[-1] = l.rstrip()[:-5]
                break
            j += 1
        text = " ".join(h.strip() for h in head).strip()
        if re.search(r"(?::|→)\s*Prop\s*$", text):
            out.append((i + 1, name.split(".")[-1], kind, name, text))
    return out


SOUND_HOMES = ("Specification/", "LinearSys/Definitions/")
TYPE_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:(structure|inductive|class)|(?:def|abbrev))\s+([^\s({\[:]+)([^\n]*)")


def type_names():
    """The last name components declared as types: structures, inductives, classes, `: Type` defs."""
    names = set()
    for p in (ROOT / "src").rglob("*.lean"):
        for raw in p.read_text(encoding="utf-8").splitlines():
            m = TYPE_DECL.match(raw)
            if m and (m.group(1) or re.search(r":\s*Type\b[^→]*(:=|$)", m.group(3))):
                names.add(m.group(2).split(".")[-1])
    return names


def explicit_binders(text, name):
    """The explicit binders `(x y : T)` after the declaration name, as (names, type) pairs."""
    rest = text.split(name, 1)[1]
    out, depth, k = [], 0, 0
    while k < len(rest):
        c = rest[k]
        if c in "{[⦃":
            depth += 1
        elif c in "}]⦄":
            depth -= 1
        elif c == "(" and depth == 0:
            d, j = 0, k
            while j < len(rest):
                d += rest[j] == "("
                d -= rest[j] == ")"
                if d == 0:
                    break
                j += 1
            m = re.match(r"\(\s*([^:()]+):\s*(.*)\)$", rest[k:j + 1])
            if m:
                out.append((m.group(1).split(), m.group(2)))
            k = j
        k += 1
    return out


def cora_methods():
    """Every CORA method name of the coverage inventory."""
    names = set()

    def walk(x):
        if isinstance(x, dict):
            for v in x.values():
                walk(v)
        else:
            for v in x:
                names.add(v) if isinstance(v, str) else walk(v)
    walk(json.loads(INVENTORY.read_text(encoding="utf-8")))
    return names


def first_word(name):
    """The leading letters of `name`, up to the next capital letter, digit or `_`."""
    return re.match(r"[A-Za-z][a-z]*", name).group(0)


def is_verb(word):
    """A third-person verb form: four letters or more, ending in `s`, not in `ss`, `us`, `is`."""
    w = word.lower()
    return len(w) >= 4 and w.endswith("s") and not w.endswith(("ss", "us", "is"))


def accepted(name, methods):
    w = first_word(name).lower()
    if w in ("is", "has") or is_verb(w):
        return True
    if name[0].islower():
        stem = re.split(r"[A-Z_0-9]", name, 1)[0]
        return name in methods or stem in methods or stem + "_" in methods
    return False


def main():
    methods = cora_methods()
    types = type_names()
    findings = []
    for p in sorted((ROOT / "src").rglob("*.lean")):
        rel = p.relative_to(ROOT)
        for ln, name, kind, full, text in prop_decls(p):
            if survey:
                print(f"{rel}:{ln}: {kind} {name}")
                continue
            if "Sound" in name and not any(h in str(rel) for h in SOUND_HOMES):
                findings.append(
                    f"{rel}:{ln}: `{name}` is a Prop-valued {kind} with `Sound` in its name — that"
                    " an object over-approximates an exact function or set is `Encloses`; `Sound`"
                    " is for the correctness bundle of an algorithm or a translation (#165)")
            if name == "Encloses" and "." in full and full.split(".")[-2] in types:
                ns = full.split(".")[-2]
                bs = explicit_binders(text, full)
                at = next((i for i, (_, t) in enumerate(bs) if re.search(rf"\b{ns}\b", t)), None)
                if at is not None and not all(
                        any(re.search(rf"\b{x}\b", bs[at][1]) for x in bs[i][0]) for i in range(at)):
                    findings.append(
                        f"{rel}:{ln}: `{full}` takes an argument before the enclosing object of type"
                        f" `{ns}` that its type does not depend on — the object comes first, then"
                        " the exact function or set, then the domain (#165)")
            if accepted(name, methods):
                continue
            findings.append(
                f"{rel}:{ln}: `{name}` is a Prop-valued {kind} — name it so that `X.{name} args` reads as"
                " a statement: `Is…`/`Has…`, or a verb relation (`Encloses`, `Holds`), or, for a CORA"
                " mirror, the CORA method's own lower-case name")
    for f in findings:
        print(f)
    sys.exit(1 if findings else 0)


main()
