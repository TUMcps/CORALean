#!/usr/bin/env python3
"""naive_float32.py -- recomputes nn-float32's unsound baseline outside Lean.

Standard library only. Every binary32 operation is a double operation rounded
to binary32 through `struct` (round to nearest, ties to even); for +, -, *, /
of two binary32 values that is the correctly rounded binary32 result, since a
double carries more than 2 * 24 + 2 significand bits. The exact network value
is computed in `fractions.Fraction`.

The network, the box and x* are the ones in
src/CORALean/Examples/Bench/NnNetwork.lean:

    y = relu(x + 2^24) - 2^24,   X = [-7/4, 1/4],   property y <= 0,   x* = 1/4.

Both naive analyses (interval bound propagation and DeepZ zonotopes) use the
same evaluation order as src/CORALean/Examples/Bench/NnNaive.lean: each dot
product summed left to right from zero, the bias added last.

Usage:
    python3 experiments/nn/naive_float32.py [<results>/nn/nn-float32.json]

Given the JSON `lake exe bench nn-float32` wrote, also checks that every number
it reports for the naive analyses and at x* agrees with this recomputation, and
exits nonzero if one does not.
"""

# Authors:       Tobias Ladner
# Written:       27-September-2026

from __future__ import annotations

import json
import struct
import sys
from fractions import Fraction


def f32(x: float) -> float:
    """Rounds a double to the nearest binary32 value (ties to even)."""
    return struct.unpack("f", struct.pack("f", x))[0]


# The network, exact: one hidden neuron x + 2^24, output h - 2^24.
W1, B1 = [[Fraction(1)]], [Fraction(2**24)]
W2, B2 = [[Fraction(1)]], [Fraction(-(2**24))]
LO, HI = [Fraction(-7, 4)], [Fraction(1, 4)]
X_STAR = [Fraction(1, 4)]
THRESHOLD = Fraction(0)


def dot(w, x, add, mul, zero):
    acc = zero
    for wj, xj in zip(w, x):
        acc = add(acc, mul(wj, xj))
    return acc


def affine(W, b, x, add, mul, zero):
    return [add(dot(row, x, add, mul, zero), bi) for row, bi in zip(W, b)]


def point_eval(W1, B1, W2, B2, x, add, mul, zero):
    h = [max(v, zero) for v in affine(W1, B1, x, add, mul, zero)]
    return affine(W2, B2, h, add, mul, zero)


def fadd(a, b):
    return f32(a + b)


def fmul(a, b):
    return f32(a * b)


def ibp_affine(W, b, lo, hi):
    out_lo, out_hi = [], []
    for row, bi in zip(W, b):
        l = u = 0.0
        for wj, lj, uj in zip(row, lo, hi):
            if wj >= 0:
                l, u = fadd(l, fmul(wj, lj)), fadd(u, fmul(wj, uj))
            else:
                l, u = fadd(l, fmul(wj, uj)), fadd(u, fmul(wj, lj))
        out_lo.append(fadd(l, bi))
        out_hi.append(fadd(u, bi))
    return out_lo, out_hi


def ibp(W1, B1, W2, B2, lo, hi):
    lo, hi = ibp_affine(W1, B1, lo, hi)
    lo, hi = [max(v, 0.0) for v in lo], [max(v, 0.0) for v in hi]
    return ibp_affine(W2, B2, lo, hi)


def zono_affine(W, b, c, G):
    c2 = affine(W, b, c, fadd, fmul, 0.0)
    G2 = [[dot(row, g, fadd, fmul, 0.0) for row in W] for g in G]
    return c2, G2


def zono_radius(c, G):
    r = [0.0] * len(c)
    for g in G:
        r = [fadd(ri, abs(gi)) for ri, gi in zip(r, g)]
    return r


def zono_relu(c, G):
    r = zono_radius(c, G)
    lam = []
    for ci, ri in zip(c, r):
        l, u = f32(ci - ri), fadd(ci, ri)
        if l >= 0:
            lam.append((1.0, 0.0))
        elif u <= 0:
            lam.append((0.0, 0.0))
        else:
            s = f32(u / f32(u - l))
            lam.append((s, f32(-fmul(s, l) / 2)))
    c2 = [fadd(fmul(s, ci), mu) for ci, (s, mu) in zip(c, lam)]
    G2 = [[fmul(s, gi) for gi, (s, _) in zip(g, lam)] for g in G]
    fresh = [[mu if j == i else 0.0 for j in range(len(lam))]
             for i, (_, mu) in enumerate(lam) if mu != 0]
    return c2, G2 + fresh


def zono(W1, B1, W2, B2, lo, hi):
    c = [f32(f32(l + u) / 2) for l, u in zip(lo, hi)]
    G = [[f32(f32(u - l) / 2) for l, u in zip(lo, hi)]]
    c, G = zono_affine(W1, B1, c, G)
    c, G = zono_relu(c, G)
    c, G = zono_affine(W2, B2, c, G)
    r = zono_radius(c, G)
    return [f32(ci - ri) for ci, ri in zip(c, r)], [fadd(ci, ri) for ci, ri in zip(c, r)]


def main() -> int:
    as32 = lambda M: [[f32(float(v)) for v in row] for row in M]
    vec32 = lambda v: [f32(float(x)) for x in v]
    w1, b1, w2, b2 = as32(W1), vec32(B1), as32(W2), vec32(B2)
    lo, hi = vec32(LO), vec32(HI)
    y_exact = point_eval(W1, B1, W2, B2, X_STAR, lambda a, b: a + b,
                         lambda a, b: a * b, Fraction(0))[0]
    y_f32 = point_eval(w1, b1, w2, b2, vec32(X_STAR), fadd, fmul, 0.0)[0]
    ibp_lo, ibp_hi = ibp(w1, b1, w2, b2, lo, hi)
    zono_lo, zono_hi = zono(w1, b1, w2, b2, lo, hi)
    print("y = relu(x + 2^24) - 2^24 on X = [-7/4, 1/4], property y <= 0")
    print(f"  x* = 1/4: exact y = {y_exact} ({float(y_exact)}), binary32 y = {y_f32}")
    for name, l, u in (("interval", ibp_lo, ibp_hi), ("zonotope", zono_lo, zono_hi)):
        verdict = "YES" if u[0] <= THRESHOLD else "no"
        print(f"  naive {name:8s} binary32: y in [{l[0]}, {u[0]}], certifies y <= 0: {verdict}")
    if len(sys.argv) < 2:
        return 0
    # the cross-check against what the Lean run wrote
    with open(sys.argv[1]) as fh:
        run = json.load(fh)
    expected = {
        "y_exact": Fraction(y_exact), "y_binary32": Fraction(y_f32),
        "interval lower": Fraction(ibp_lo[0]), "interval upper": Fraction(ibp_hi[0]),
        "zonotope lower": Fraction(zono_lo[0]), "zonotope upper": Fraction(zono_hi[0]),
    }
    parse = lambda s: Fraction(int(s.split("/2^")[0]), 2 ** int(s.split("/2^")[1]))
    got = {"y_exact": parse(run["y_exact"]["exact"]),
           "y_binary32": parse(run["y_binary32"]["exact"])}
    for a in run["analyses"]:
        if not a["sound"]:
            got[a["method"] + " lower"] = parse(a["y_lower"]["exact"])
            got[a["method"] + " upper"] = parse(a["y_upper"]["exact"])
    bad = [k for k in expected if got.get(k) != expected[k]]
    for k in expected:
        print(f"  {k:15s} python {expected[k]!s:>6}  lean {got.get(k)!s:>6}")
    print("cross-check: " + ("MISMATCH in " + ", ".join(bad) if bad else "all agree"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
