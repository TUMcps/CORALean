#!/usr/bin/env python3
"""A `noncomputable` declaration is justified in the file, not on a list (issue #257).

    python3 scripts/check-noncomputable.py

Keep `noncomputable` to a minimum: a definition computes wherever it can, and where the real
version cannot, there is at least a float variant that does. A `noncomputable` declaration is
allowed when it is

  * in a real layer: a file under a `Real/` folder, or a declaration that works over ℝ rather than
    over the float scalar `𝕋`, or
  * a `Set`, a `Prop` or ℝ-valued (its type says it is a specification, which no machine runs), or
  * documented: its docstring says why it cannot compute (a choice, an integral, an infimum, a
    limit, a derivative, ...).

In the float layer (a `Float/` folder, a file or declaration named `...Float`, a declaration over
`𝕋`) it is never allowed. `noncomputable section` is refused by `check-conventions.sh`.

A declaration "works over ℝ" when its text mentions ℝ (or `Real`) and uses `𝕋` at most as the index
of a system or a class (`LinearSys 𝕋 n`, `Location S G L 𝕋 n`), never as the type of a value
(`Vec 𝕋 n`, `x : 𝕋`).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*)"
                  r"(def|abbrev|instance|opaque|example)\b\s*(\S*)")
# What ends a declaration at column 0.
START = re.compile(r"^(?:@\[|/--|/-!|/-|--|(?:private |protected |noncomputable |nonrec |partial |unsafe |scoped )*"
                   r"(?:def|abbrev|instance|theorem|lemma|structure|class|inductive|opaque|axiom|example|"
                   r"namespace|end|section|variable|open|set_option|attribute|macro|notation|local|infix|"
                   r"syntax|elab|assert_not|omit|include)\b)")
REAL = re.compile(r"ℝ|\bReal\b|EReal|NNReal|\btoReal(?:Mat|Vec)?\b")
# `𝕋` as the type of a value: an argument of a container, a binder's type, a function's end.
SCALAR_DATA = re.compile(r"(?:\b(?:Vec|Mat|Interval|WithTop|Option|List|Array|Fin \S+ →|ℐ)\s*\(?\s*𝕋)"
                         r"|(?:[:→(]\s*𝕋(?![\w₀-₉']))|(?:𝕋\s*→)")
# Why a definition cannot compute: the word a docstring uses for it.
REASON = re.compile(
    r"\bchoice\b|\bchooses?\b|\bchosen\b|\bClassical\b|\bintegral|\binfimum\b|\bsupremum\b|\bsInf\b|\bsSup\b|"
    r"\blimit\b|\bderivative\b|\bfderiv\b|\bnot computable\b|\buncomputable\b|\bnoncomputable(?::|\s+because|\s+since)|"
    r"\bcannot (?:be )?comput|\bnot compute\b|\bno (?:algorithm|float)\b",
    re.I)


def codomain(h):
    """The type after the last top-level `:` and `→` of a declaration header, or None."""
    h = re.sub(r":=.*$", "", h, flags=re.S)
    h = re.sub(r"\swhere\b.*$", "", h, flags=re.S)
    h = re.sub(r"\n\s*\|.*$", "", h, flags=re.S)
    d, cut = 0, -1
    for i, c in enumerate(h):
        if c in "({[⟨":
            d += 1
        elif c in ")}]⟩":
            d -= 1
        elif c == ":" and d == 0 and h[i + 1:i + 2] != "=":
            cut = i
    if cut < 0:
        return None
    t = h[cut + 1:]
    d, seg = 0, t
    for i, c in enumerate(t):
        if c in "({[⟨":
            d += 1
        elif c in ")}]⟩":
            d -= 1
        elif d == 0 and c == "→":
            seg = t[i + 1:]
    return seg.strip()


def header(lines, i):
    """The declaration's text up to its `:=` or `where`."""
    h = lines[i]
    j = i
    while not re.search(r":=|\swhere\b|\s\|", h) and j + 1 < len(lines) and j < i + 25:
        j += 1
        h += "\n" + lines[j]
    return h


def block(lines, i):
    out = [lines[i]]
    for l in lines[i + 1:]:
        if l and not l[0].isspace() and START.match(l):
            break
        out.append(l)
    return "\n".join(out)


def docstring(lines, i):
    k = i - 1
    while k >= 0 and re.match(r"\s*(@\[|set_option\b)", lines[k]):
        k -= 1
    if k < 0 or not lines[k].rstrip().endswith("-/"):
        return ""
    e = k
    while k >= 0 and not lines[k].lstrip().startswith("/--"):
        k -= 1
    return "\n".join(lines[max(k, 0):e + 1]) if k >= 0 else ""


def code(text):
    return "\n".join(re.sub(r"--.*$", "", l) for l in text.split("\n"))


def layer(rel, h, cod, b, ctx):
    """`float`, `scalar`, `real` or `neutral` for a declaration. A `Float/` folder is the float
    layer unless it is a `Theorems/` file, which states things about floats and never runs; a
    declaration is over `𝕋` when its result is a value of `𝕋`, not when it merely reads one."""
    if "/Real/" in rel:
        return "real"
    if "/Float/" in rel and "/Theorems/" not in rel:
        return "float"
    if SCALAR_DATA.search(code(": " + cod if cod is not None else h)):
        return "scalar"
    if REAL.search(code(b)) or REAL.search(ctx):
        return "real"
    return "neutral"


def is_spec(cod):
    """A `Set`, a `Prop` or an ℝ-valued type."""
    return cod is not None and (cod == "Prop" or re.match(r"Set\b", cod) is not None
                                or re.match(r"(ℝ|EReal|ℝ≥0∞?|NNReal)$", cod) is not None)


def findings(files=None):
    out = []
    paths = files if files is not None else sorted(SRC.glob("CORALean/**/*.lean"))
    for p in paths:
        text = p.read_text(encoding="utf-8")
        if "noncomputable" not in text:
            continue
        rel = p.relative_to(ROOT).as_posix()
        lines = text.split("\n")
        # the `variable` lines and a `CORALean.Real` namespace: the ambient a declaration is stated over
        ctx = code("\n".join(l for l in lines if l.startswith(("variable", "namespace CORALean.Real"))))
        for i, line in enumerate(lines):
            m = DECL.match(line)
            if not m or "noncomputable" not in m.group(1):
                continue
            name = m.group(3)
            h = header(lines, i)
            b = block(lines, i)
            cod = codomain(h)
            lay = layer(rel, h, cod, b, ctx)
            where = f"{rel}:{i + 1}: `noncomputable {m.group(2)} {name}`"
            if lay == "float":
                out.append(f"{where} in the float layer — it must compute; make it computable")
            elif lay == "scalar" and not is_spec(cod):
                out.append(f"{where} is over the float scalar `𝕋` — it must compute; make it computable")
            elif lay == "real" or is_spec(cod) or REASON.search(docstring(lines, i)):
                continue
            else:
                out.append(f"{where} is not in a real layer, not a `Set`/`Prop`/ℝ-valued, and its"
                           " docstring does not say why it cannot compute — make it computable, or say why")
    return out


if __name__ == "__main__":
    res = findings()
    for r in res:
        print(r)
    sys.exit(1 if res else 0)
