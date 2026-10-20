#!/usr/bin/env python3
"""The inputs and outputs of a content file's main declaration are listed in its module docstring (#251).

In the module docstring of a content file whose main declaration (the first declaration under
its `MAIN THEOREM` / `MAIN DEFINITION` banner) is

* a definition (`def`, `abbrev`, `structure`, `inductive`): `## Inputs` and `## Output`, plus
  `## Hypotheses` between them when the declaration has `Prop` binders;
* a theorem (`theorem`, `lemma`): `## Inputs`, `## Hypotheses` and `## Conclusion`.

`## Inputs` lists the non-`Prop` binders `(x : T)`, `{x : T}`, `⦃x : T⦄` of the declaration as
`* `x` – description`, named exactly as in the declaration and in its order, none missing and none
extra; an anonymous binder `(_ : T)` is listed as `_`; instance binders `[..]` and everything that comes from a `variable` line are not binders of
the declaration and not listed. `## Hypotheses` lists the `Prop` binders the same way.
`## Output` / `## Conclusion` has exactly one `*` entry. A section with nothing to list says
`* none`. The sections come last, after the prose and before `## References`.

Exempt: `Basic.lean`, `API.lean`, `Instances.lean`, `Interfaces.lean`, and every file with no
`MAIN THEOREM` / `MAIN DEFINITION` banner (`MAIN TYPE`, `MAIN INSTANCE`, `INSTANCES`, files that
declare nothing). Files not yet converted are listed in `scripts/io-doc-allowlist.txt`, one path
per line; the list only shrinks, and an entry whose file now conforms (or is exempt, or gone) is
reported as stale.

Which binder is a `Prop` is decided by a text proxy, since no elaboration happens here. A binder
is a hypothesis when
  * its name is `h` alone or `h` followed by at least one more character (`hZ`, `hlt`, `h₁`,
    `hΔt`) and its type does not begin with a data head (`ℕ ℤ ℝ ℚ ℂ Bool Fin Type Set Vec Mat
    List Finset Option String`, or the float scalar `𝕋`: `{lo hi : 𝕋}`; a function type `α → 𝕋` counts by its codomain) free of a depth-0 relation symbol (so `(hi : Fin k → Vec 𝕋 n)`
    is an input, `(hS : Set.Nonempty S)` and `(hS : Set α ⊆ T)` are hypotheses), or
  * its type, outer parentheses removed, contains at depth 0 one of
    `= ≠ ≤ ≥ < > ∈ ∉ ⊆ ⊂ ⊇ ⊃ ∣ ∀ ∃ ¬ ∧ ∨ ↔ ⊥` (`→` is not in the list: it is a function type
    as often as an implication), or
  * its type's head identifier is `Is…`/`Has…` (also after a namespace, `Zonotope.IsFoo`), or one
    of a short list of Mathlib predicates (`Convex`, `Continuous`, `Nonempty`, …) or the type is
    `x.Nonempty`-style with such a trailing component.
Known limits: a `Prop` binder with a name not starting with `h`, a type with no listed operator
and a head not listed (`(P : Foo Z)` for a `Prop` structure `Foo`) is taken for an input; a data
binder named `h…` whose type is headed by a data type but contains a depth-0 relation symbol
(`(hull : Set X ⊆ ..)`) is taken for a hypothesis; a data binder whose type has a depth-0 relation symbol in an unparenthesised
set-builder is taken for a hypothesis. The cure for each is to rename the binder, or to put the
file on the allowlist and say why in the issue.

The number types `ℝ≥0∞`, `ℝ≥0`, `ℚ≥0` are read as plain number types: their `≥` is not a relation
symbol. (Without this, `(f : α → ℝ≥0∞)` was sorted into the hypotheses.) A dependent family
`(hy : (i : Fin N) → Vec ℝ (qy i))` is judged by its codomain, so it is data, not a hypothesis.
A function binder `(contract : ∀ m : ℕ, A → B → (Fin m → ℝ) × (Fin m → ℝ))` — a `∀` whose body
has no relation symbol and ends in a parenthesised codomain — is data (a contractor), not a statement.

An entry whose description is only a backticked expression longer than 15 characters is
rejected: it repeats the signature; say it in words. Inputs/Hypotheses entries read exactly
`* `name` – description`.

`--root DIR` reads another tree (used to test the rule on a mutated copy). Prints findings and
exits 1 on any.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
args = sys.argv[1:]
if "--root" in args:
    ROOT = Path(args[args.index("--root") + 1]).resolve()
LIST = ROOT / "scripts/io-doc-allowlist.txt"

EXEMPT_NAMES = {"Basic.lean", "API.lean", "Instances.lean", "Interfaces.lean"}
BANNER = re.compile(r"^-- =+  MAIN (THEOREM|DEFINITION)  =+ --$")
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|scoped|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+(\S+)"
)
HEADING = re.compile(r"^##\s+(Inputs|Hypotheses|Output|Conclusion|References)\s*$")
OPEN, CLOSE = "([{⦃⟨", ")]}⦄⟩"
PROP_SYMBOLS = "=≠≤≥<>∈∉⊆⊂⊇⊃∣∀∃¬∧∨↔⊥"
PROP_HEADS = {
    "Convex", "StrictConvex", "Continuous", "ContinuousOn", "ContinuousAt", "Differentiable",
    "DifferentiableOn", "DifferentiableAt", "ContDiff", "ContDiffOn", "Nonempty", "Finite",
    "Injective", "Surjective", "Bijective", "StrictMono", "Monotone", "Antitone", "MonotoneOn",
    "Disjoint", "Even", "Odd", "Prime", "Measurable", "Summable", "BddAbove", "BddBelow",
    "Pairwise", "LinearIndependent", "Integrable", "IntegrableOn", "AEMeasurable", "HasFDerivAt",
    "HasDerivAt", "HasFDerivWithinAt", "HasDerivWithinAt", "IsClosed", "IsOpen", "IsCompact",
    "True", "False", "Fact", "Tendsto", "Set.Finite", "Set.Nonempty", "Function.Injective",
    "Function.Surjective", "Function.Bijective", "Set.Countable", "Nat.Prime", "Set.InjOn",
    "Set.SurjOn", "Set.BijOn", "Set.MapsTo", "Set.Subsingleton", "Antitone", "AntitoneOn",
    "StrictMonoOn", "StrictAnti", "StrictAntiOn", "Symmetric", "Matrix.PosSemidef", "PosSemidef",
    "PosDef", "Matrix.PosDef", "Equivalence",
}


def strip_comments(text):
    """Line comments `-- ...` removed (the CONCL/PROOF flags are line comments too)."""
    return "\n".join(re.sub(r"\s*--.*$", "", l) for l in text.split("\n"))


def matching(s, i):
    """Index of the bracket closing the one at `s[i]`, or -1."""
    d = 0
    for k in range(i, len(s)):
        if s[k] in OPEN:
            d += 1
        elif s[k] in CLOSE:
            d -= 1
            if d == 0:
                return k
    return -1


def top_level(s):
    """`s` with every bracketed part blanked out, same length, so depth-0 scans are plain."""
    out, d = [], 0
    for c in s:
        if c in OPEN:
            d += 1
            out.append(" ")
        elif c in CLOSE:
            d -= 1
            out.append(" ")
        else:
            out.append(c if d == 0 else " ")
    return "".join(out)


def binders(sig):
    """`[(name, type)]` of the explicit/implicit/strict-implicit binders at the head of `sig`
    (the text after the declaration name), up to the colon, `:=`, `where` or `|` that ends them."""
    out, i, n = [], 0, len(sig)
    while i < n:
        while i < n and sig[i].isspace():
            i += 1
        if i >= n or sig[i] not in "({⦃[":
            break
        j = matching(sig, i)
        if j < 0:
            break
        inner = sig[i + 1:j]
        if sig[i] != "[":
            flat = top_level(inner)
            m = re.search(r":(?!=)", flat)
            if m:
                names, typ = inner[:m.start()], inner[m.end():]
                d = re.search(r":=", top_level(typ))
                if d:
                    typ = typ[:d.start()]
            else:
                names, typ = inner, ""
            for nm in names.split():
                out.append((nm, typ.strip()))
        i = j + 1
    return out


DATA_HEADS = {"ℕ", "ℤ", "ℝ", "ℚ", "ℂ", "Bool", "Fin", "Type", "Type*", "Sort", "Prop", "String",
              "List", "Finset", "Set", "Vec", "Mat", "Option", "𝕋"}


def is_prop(name, typ):
    t = typ.strip()
    # a dependent family `(i : Fin N) → T` is judged by its codomain `T`
    while True:
        m = re.match(r"\(\w+ : [^()]*(?:\([^()]*\)[^()]*)*\)\s*→\s*", t)
        if not m:
            break
        t = t[m.end():]
    head0 = re.match(r"[^\s(]+", t)
    # a name `h…` is a hypothesis, unless its type is headed by a data type with no relation
    # symbol at depth 0 (`(hi : Fin k → Vec 𝕋 n)`, `(h : ℕ)`)
    if name == "h" or re.match(r"^h.", name):
        data = bool(head0 and head0.group(0) in DATA_HEADS)
        if not data:
            # a function type `α → 𝕋` is data when its codomain is
            flat0 = top_level(t)
            k = flat0.rfind("→")
            if k >= 0:
                cod = re.match(r"[^\s(]+", t[k + 1:].strip())
                data = bool(cod and cod.group(0) in DATA_HEADS)
        if not (data and not any(c in re.sub(r"[ℝℚ]≥0∞?", "ℝ", top_level(t)) for c in PROP_SYMBOLS)):
            return True
    while t.startswith("(") and matching(t, 0) == len(t) - 1:
        t = t[1:-1].strip()
    # a function binder `∀ m : ℕ, A → B` (no relation symbol in its body, a function type whose
    # last component is a parenthesised or product type) is data: a contractor, not a statement
    if t.startswith("∀"):
        comma = top_level(t).find(",")
        body = t[comma + 1:].strip() if comma >= 0 else ""
        flat_body = re.sub(r"[ℝℚ]≥0∞?", "ℝ", top_level(body))
        k = flat_body.rfind("→")
        if k >= 0 and not any(c in flat_body for c in PROP_SYMBOLS) and body[k + 1:].strip().startswith("("):
            return False
    # `ℝ≥0∞` / `ℝ≥0` / `ℚ≥0` are number types, not the relation `≥`
    flat = re.sub(r"[ℝℚ]≥0∞?", "ℝ", top_level(t))
    # a function type `A → B` is a hypothesis only when its last component is one
    if any(c in flat for c in PROP_SYMBOLS):
        return True
    head = re.match(r"[^\s(]+", t)
    if head:
        h = head.group(0)
        last = h.split(".")[-1]
        if re.match(r"^(Is|Has)[A-Z]", last) or h in PROP_HEADS or last in PROP_HEADS:
            return True
    return False


def split_binders(sig):
    b = binders(sig)
    ins = [n for n, t in b if not is_prop(n, t)]
    hyps = [n for n, t in b if is_prop(n, t)]
    return ins, hyps


def module_doc(lines):
    """(start, end) line indices of the module docstring, or None."""
    for i, l in enumerate(lines):
        if l.startswith("/-!"):
            for j in range(i, len(lines)):
                if "-/" in lines[j] and (j > i or lines[j].rstrip().endswith("-/")):
                    return i, j
            return None
    return None


def main_declaration(lines):
    """(keyword, name, text after the name up to its end) of the declaration under the first
    MAIN THEOREM/DEFINITION banner, or None."""
    for i, l in enumerate(lines):
        if BANNER.match(l):
            inblock = False
            for j in range(i + 1, len(lines)):
                s = lines[j]
                if inblock:
                    if "-/" in s:
                        inblock = False
                    continue
                if s.lstrip().startswith("/-"):
                    if "-/" not in s:
                        inblock = True
                    continue
                m = DECL.match(s)
                if m:
                    body = []
                    for k in range(j, min(j + 60, len(lines))):
                        body.append(lines[k])
                        if k > j and re.match(r"^\S", lines[k]) and not lines[k].startswith("--"):
                            body.pop()
                            break
                    text = strip_comments("\n".join(body))
                    k = text.index(m.group(2), m.start(2)) + len(m.group(2))
                    return m.group(1), m.group(2), text[k:]
                if s.strip() and not s.lstrip().startswith(("--", "@[")):
                    return None
            return None
    return None


def sections(doc):
    """{heading: [entry lines]} in order of appearance, plus the heading order."""
    order, cur, body = [], None, {}
    for l in doc:
        m = HEADING.match(l)
        if m:
            cur = m.group(1)
            order.append(cur)
            body.setdefault(cur, [])
        elif re.match(r"^#+\s", l) or l.strip() == "-/":
            cur = None
        elif cur and l.strip():
            body[cur].append(l)
    return order, body


def entries(lines):
    return [l for l in lines if l.startswith("* ")]


def listed(lines):
    names = []
    for e in entries(lines):
        if e.rstrip() == "* none":
            continue
        m = re.match(r"^\* `([^`]+)`", e)
        names.append(m.group(1) if m else None)
    return names


FILLER = {"parameter", "argument", "input", "value", "result", "output", "hypothesis",
          "assumption", "conclusion", "statement"}


def bad_description(desc, minwords=0):
    """Why a description is unacceptable (empty, placeholder, generic filler, too short), or None."""
    d = desc.strip().strip("`").strip()
    if not d:
        return "empty"
    low = d.lower()
    if re.search(r"add description|\btodo\b|\btbd\b|\bfixme\b", low) or re.fullmatch(r"[.…\s-]+", d):
        return "placeholder"
    words = [w for w in re.findall(r"[a-z]+", low) if w not in ("a", "an", "the")]
    if " ".join(words) in FILLER:
        return "generic filler"
    m = re.fullmatch(r"`([^`]*)`\.?", desc.strip())
    if m and len(m.group(1)) > 15:
        return "only a formula (say it in words)"
    if len(desc.split()) < minwords:
        return f"too short (need {minwords} words)"
    return None


def check(path, text):
    """Findings for one non-exempt file; each a `line: message`."""
    lines = text.split("\n")
    md = main_declaration(lines)
    if md is None:
        return None  # nothing to document
    kw, name, sig = md
    if kw in ("instance", "class"):
        return None
    theorem = kw in ("theorem", "lemma")
    ins, hyps = split_binders(sig)
    doc = module_doc(lines)
    if doc is None:
        return ["1: no module docstring"]
    start, end = doc
    order, body = sections(lines[start:end + 1])
    where = start + 1
    out = []
    want = ["Inputs"]
    if theorem or hyps:
        want.append("Hypotheses")
    want.append("Conclusion" if theorem else "Output")
    bad = "Output" if theorem else "Conclusion"
    if bad in order:
        out.append(f"{where}: a {'theorem' if theorem else 'definition'} has `## "
                   f"{'Conclusion' if theorem else 'Output'}`, not `## {bad}`")
    mine = [h for h in order if h != "References"]
    if "Hypotheses" in mine and not (theorem or hyps):
        out.append(f"{where}: `## Hypotheses` but `{name}` has no `Prop` binder")
    if [h for h in mine if h != bad] != want:
        out.append(f"{where}: sections must be, in order, " + ", ".join(f"`## {h}`" for h in want)
                   + " (then `## References`), after the prose; found "
                   + (", ".join(f"`## {h}`" for h in mine) or "none"))
        return out
    if "References" in order and order.index("References") != len(order) - 1:
        out.append(f"{where}: `## References` comes last")
    for sec, exp in (("Inputs", ins), ("Hypotheses", hyps)):
        if sec not in want:
            continue
        got = listed(body[sec])
        if None in got:
            out.append(f"{where}: `## {sec}` entries read `* `name` – description`")
        elif got != exp:
            out.append(f"{where}: `## {sec}` lists {got or 'nothing'} but `{name}` has "
                       f"{exp or 'none (write `* none`)'}, in that order")
        for e in entries(body[sec]):
            if e.rstrip() == "* none":
                continue
            m = re.match(r"^\* `[^`]+` – (.*)$", e)
            why = bad_description(m.group(1)) if m else "malformed (reads `* `name` – description`)"
            if why:
                out.append(f"{where}: `## {sec}` entry description is {why}: {e.strip()}")
    last = "Conclusion" if theorem else "Output"
    if len(entries(body[last])) != 1:
        out.append(f"{where}: `## {last}` has {len(entries(body[last]))} entries, exactly one")
    else:
        why = bad_description(entries(body[last])[0][2:], 3)
        if why:
            out.append(f"{where}: `## {last}` entry is {why}: {entries(body[last])[0].strip()}")
    return out


def files():
    for p in sorted((ROOT / "src").rglob("*.lean")):
        if p.name in EXEMPT_NAMES:
            continue
        yield p


def main():
    allow = {}
    if LIST.exists():
        for n, l in enumerate(LIST.read_text(encoding="utf-8").splitlines(), 1):
            if l.strip() and not l.startswith("#"):
                allow[l.strip()] = n
    findings, seen, hit = [], set(), set()
    for p in files():
        rel = p.relative_to(ROOT).as_posix()
        text = p.read_text(encoding="utf-8")
        res = check(rel, text)
        seen.add(rel)
        if res is None:
            continue
        if rel in allow:
            if res:
                hit.add(rel)
            continue
        for r in res:
            findings.append(f"{rel}:{r}")
    for rel, n in allow.items():
        if rel not in seen:
            findings.append(f"scripts/io-doc-allowlist.txt:{n}: stale entry `{rel}` — no such file")
        elif rel not in hit:
            findings.append(f"scripts/io-doc-allowlist.txt:{n}: stale entry `{rel}` — the file "
                            f"conforms or is exempt; the list only shrinks")
    if "--list" in args:
        print("\n".join(sorted(hit | {f.split(":")[0] for f in findings if f.startswith("src/")})))
        return 0
    if findings:
        print("\n".join(findings))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
