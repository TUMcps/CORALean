#!/usr/bin/env python3
"""Independent soundness check for `lake exe oracle`'s responses.

Re-reads `requests.jsonl` and the oracle's own output (one line of `Json` per
request, in the same order) and checks, in exact `fractions.Fraction`
arithmetic -- never floats:

* `from`: the returned value equals the input exactly.
* `roundTo` (a matrix `x`): `x - value` lies in `[error.inf, error.sup]`.
* Every zonotope-valued op (`roundTo`-`Z`, `mtimes`, `mtimesInterval`, `plus`,
  `plusBox`/`plusInterval`, `linComb`, `reduce`, `enclosure`): the *exact*
  result's interval hull is a subset of the *output*'s hull, coordinatewise.
  A hull is `c ± Σ_l |G_il| ± [E.inf, E.sup]` (`hull`), and the exact result is
  computed straight from the request, one shape per op (`exact_hull_*`):
  `roundTo`/`reduce`/`enclosure` leave the set unchanged, so it is the
  *input*'s own hull; `plus`/`plusBox` add hulls, exact since a Minkowski
  sum's hull is the sum of the operands' hulls, coordinatewise, for any two
  sets; `linComb` is the coordinatewise union of the two hulls (segments
  between a pair of extreme points reach no further than whichever operand's
  own extreme is larger); `mtimes` maps the hull's zonotope part by the exact
  matrix and its error box through exact interval-matrix-vector arithmetic,
  both exact since `M` has no width. `mtimesInterval` cannot be made exact
  this cheaply -- the true set is a bilinear image of `Z`'s exact shape by an
  interval matrix -- so it collapses `Z` to its own hull first and runs
  ordinary interval arithmetic on that box against the interval matrix: sound
  (a superset of the true tight hull), so the containment check stays a
  *necessary* condition rather than an exact one, same as the rest.

Every check names the request `id` and the violated bound on failure. Uses
only the standard library.
"""

# Authors:       Tobias Ladner
# Written:       30-September-2026
# Last update:   01-October-2026
# Last revision: ---


# ----------------------------------------  BEGIN CODE  ---------------------------------------- #

import json
import sys
from fractions import Fraction as F


# -----------------------------------------  AUXILIARY  ----------------------------------------- #

def parse_scalar(s) -> F:
    """A wire scalar (`"m*2^e"`, `"m*10^e"`, a plain integer string, or a JSON number) as an
    exact `Fraction` -- the same shapes `Oracle/Codec.lean` and `Oracle/Dtype.lean` emit; `e`'s
    sign is read by `int()` either way, so `"m*10^-d"` (the fixedpoint output grammar) and
    `"m*10^3"` (an integer, accepted everywhere) both parse here."""
    if isinstance(s, (int, float)):
        return F(s)
    if "*2^" in s:
        m, e = s.split("*2^")
        m, e = int(m), int(e)
        return F(m) * (F(2) ** e)
    if "*10^" in s:
        m, e = s.split("*10^")
        m, e = int(m), int(e)
        return F(m) * (F(10) ** e)
    return F(int(s))


def parse_mat(m):
    """`{"rows","cols","data"}` as `(r, c, [[Fraction]])`, row-major."""
    r, c = m["rows"], m["cols"]
    data = [parse_scalar(x) for x in m["data"]]
    return r, c, [[data[i * c + j] for j in range(c)] for i in range(r)]


def parse_vec(m):
    r, c, d = parse_mat(m)
    assert c == 1, f"expected a column vector, got {r}x{c}"
    return [d[i][0] for i in range(r)]


def parse_zonotope(z):
    c = parse_vec(z["c"])
    _, h, G = parse_mat(z["G"])
    einf = parse_vec(z["E"]["inf"])
    esup = parse_vec(z["E"]["sup"])
    return c, h, G, einf, esup


def hull(c, h, G, einf, esup):
    """The interval hull `c ± Σ|G| ± E`, coordinatewise -- `Zonotope.interval`'s own formula,
    over ℚ rather than a rounded `𝕋`. Exact: a zonotope's own axis-aligned extent is achieved by
    some point of its construct, generator coefficients and the error box chosen independently
    per coordinate."""
    n = len(c)
    radius = [sum(abs(G[i][j]) for j in range(h)) for i in range(n)]
    lo = [c[i] - radius[i] + einf[i] for i in range(n)]
    hi = [c[i] + radius[i] + esup[i] for i in range(n)]
    return lo, hi


def hull_of_zonotope_json(z):
    return hull(*parse_zonotope(z))


def hull_subset(lo1, hi1, lo2, hi2):
    return all(lo2[i] <= lo1[i] and hi1[i] <= hi2[i] for i in range(len(lo1)))


def mat_vec(M, v):
    return [sum(M[i][j] * v[j] for j in range(len(v))) for i in range(len(M))]


def interval_mul(a_lo, a_hi, b_lo, b_hi):
    """`[a_lo,a_hi] * [b_lo,b_hi]`, exact: the min/max of the four corner products."""
    products = (a_lo * b_lo, a_lo * b_hi, a_hi * b_lo, a_hi * b_hi)
    return min(products), max(products)


def check_hull_subset(label, req_id, exact_lo, exact_hi, out_lo, out_hi, fails):
    if not hull_subset(exact_lo, exact_hi, out_lo, out_hi):
        fails.append(f"id {req_id}: {label}: exact hull {list(zip(exact_lo, exact_hi))} "
                      f"not inside output hull {list(zip(out_lo, out_hi))}")


# -------------------------------------  EXACT RESULT HULLS  ------------------------------------ #

def exact_hull_unchanged(req, _resp):
    """`roundTo`(`Z`)/`reduce`/`enclosure`: the represented set does not change. -/"""
    return hull_of_zonotope_json(req["Z"])


def exact_hull_mtimes(req, _resp):
    """`M · Z`, `M` an exact matrix: the generators map exactly (`M @ G`), and so does the
    error box, an exact matrix times an interval being the ordinary one-sided case of
    `interval_mul`."""
    c, h, G, einf, esup = parse_zonotope(req["Z"])
    _, _, M = parse_mat(req["M"])
    n, m = len(c), len(M)
    new_c = mat_vec(M, c)
    new_G = [[sum(M[i][j] * G[j][l] for j in range(n)) for l in range(h)] for i in range(m)]
    new_radius = [sum(abs(new_G[i][l]) for l in range(h)) for i in range(m)]
    e_lo, e_hi = [], []
    for i in range(m):
        lo_i = hi_i = F(0)
        for j in range(n):
            plo, phi = interval_mul(M[i][j], M[i][j], einf[j], esup[j])
            lo_i, hi_i = lo_i + plo, hi_i + phi
        e_lo.append(lo_i)
        e_hi.append(hi_i)
    exact_lo = [new_c[i] - new_radius[i] + e_lo[i] for i in range(m)]
    exact_hi = [new_c[i] + new_radius[i] + e_hi[i] for i in range(m)]
    return exact_lo, exact_hi


def exact_hull_mtimes_interval(req, _resp):
    """A sound *outer* bound, not the tight hull: `Z` collapsed to its own hull box first, then
    ordinary interval-matrix-vector arithmetic against `M` -- see the module docstring."""
    zlo, zhi = hull_of_zonotope_json(req["Z"])
    _, _, Mlo = parse_mat(req["M"]["inf"])
    _, _, Mhi = parse_mat(req["M"]["sup"])
    n, m = len(zlo), len(Mlo)
    exact_lo, exact_hi = [], []
    for i in range(m):
        lo_i = hi_i = F(0)
        for j in range(n):
            plo, phi = interval_mul(Mlo[i][j], Mhi[i][j], zlo[j], zhi[j])
            lo_i, hi_i = lo_i + plo, hi_i + phi
        exact_lo.append(lo_i)
        exact_hi.append(hi_i)
    return exact_lo, exact_hi


def exact_hull_plus(req, _resp):
    """`Z + Z2`: a Minkowski sum's hull is the sum of the operands' hulls, exact for any sets."""
    lo1, hi1 = hull_of_zonotope_json(req["Z"])
    lo2, hi2 = hull_of_zonotope_json(req["Z2"])
    return [a + b for a, b in zip(lo1, lo2)], [a + b for a, b in zip(hi1, hi2)]


def exact_hull_plus_box(req, _resp):
    """`Z + I`, `I` a box: the same Minkowski-sum argument as `plus`, `I` its own hull."""
    lo1, hi1 = hull_of_zonotope_json(req["Z"])
    iinf = parse_vec(req["I"]["inf"])
    isup = parse_vec(req["I"]["sup"])
    return [a + b for a, b in zip(lo1, iinf)], [a + b for a, b in zip(hi1, isup)]


def exact_hull_lincomb(req, _resp):
    """`linComb(Z,Z2)` (`segments`, not the convex hull): the coordinatewise union of the two
    hulls -- a linear interpolation between two extremes reaches no further than whichever
    extreme is larger, so the sup/inf over `λ ∈ [0,1]` is attained at `λ ∈ {0,1}`."""
    lo1, hi1 = hull_of_zonotope_json(req["Z"])
    lo2, hi2 = hull_of_zonotope_json(req["Z2"])
    return [min(a, b) for a, b in zip(lo1, lo2)], [max(a, b) for a, b in zip(hi1, hi2)]


EXACT_HULLS = {
    "roundTo": exact_hull_unchanged,
    "mtimes": exact_hull_mtimes,
    "mtimesInterval": exact_hull_mtimes_interval,
    "plus": exact_hull_plus,
    "plusBox": exact_hull_plus_box,
    "plusInterval": exact_hull_plus_box,
    "linComb": exact_hull_lincomb,
    "reduce": exact_hull_unchanged,
    "enclosure": exact_hull_unchanged,
}


# -----------------------------------------  ONE CHECK  ------------------------------------------ #

def check_from(req, resp, fails):
    _, _, xs = parse_mat(req["x"])
    _, _, vs = parse_mat(resp["value"])
    for i, row in enumerate(xs):
        for j, xv in enumerate(row):
            if xv != vs[i][j]:
                fails.append(f"id {req.get('id')}: from: entry ({i},{j}) {xv} != {vs[i][j]}")


def check_round_to_mat(req, resp, fails):
    _, _, xs = parse_mat(req["x"])
    _, _, vs = parse_mat(resp["value"])
    _, _, los = parse_mat(resp["error"]["inf"])
    _, _, his = parse_mat(resp["error"]["sup"])
    for i, row in enumerate(xs):
        for j, xv in enumerate(row):
            err = xv - vs[i][j]
            if not (los[i][j] <= err <= his[i][j]):
                fails.append(f"id {req.get('id')}: roundTo: entry ({i},{j}): "
                              f"x-value={err} not in [{los[i][j]},{his[i][j]}]")


def check_interval(req, resp, fails):
    lo, hi = hull_of_zonotope_json(req["Z"])
    _, _, infM = parse_mat(resp["interval"]["inf"])
    _, _, supM = parse_mat(resp["interval"]["sup"])
    inf = [infM[i][0] for i in range(len(infM))]
    sup = [supM[i][0] for i in range(len(supM))]
    if inf != lo or sup != hi:
        fails.append(f"id {req.get('id')}: interval: got ({inf},{sup}), expected ({lo},{hi})")


def check_zonotope_hull(op, req, resp, fails):
    """Every zonotope-valued op: `EXACT_HULLS[op]`'s exact hull must sit inside the response's
    own -- `roundTo` is `exact_hull_unchanged` too, since a rounded `Z` denotes what it was."""
    exact_lo, exact_hi = EXACT_HULLS[op](req, resp)
    out_lo, out_hi = hull_of_zonotope_json(resp["Z"])
    check_hull_subset(op, req.get("id"), exact_lo, exact_hi, out_lo, out_hi, fails)
    if op == "enclosure":
        einf = parse_vec(resp["Z"]["E"]["inf"])
        esup = parse_vec(resp["Z"]["E"]["sup"])
        if any(x != 0 for x in einf) or any(x != 0 for x in esup):
            fails.append(f"id {req.get('id')}: enclosure: E is not exactly zero: "
                          f"inf={einf} sup={esup}")


# =======================================  MAIN DEFINITION  ===================================== #

def main() -> int:
    if len(sys.argv) != 3:
        print("usage: check_sound.py requests.jsonl output.jsonl", file=sys.stderr)
        return 2
    with open(sys.argv[1]) as f:
        req_lines = [line for line in f if line.strip()]
    with open(sys.argv[2]) as f:
        resp_lines = [line for line in f if line.strip()]
    fails: list[str] = []
    checked = 0
    for rline, oline in zip(req_lines, resp_lines):
        try:
            req = json.loads(rline)
        except json.JSONDecodeError:
            continue  # the malformed-JSON regression line: nothing to check against
        resp = json.loads(oline)
        if not resp.get("ok"):
            continue  # an expected error: nothing exact to compare
        op = req.get("op")
        try:
            if op == "from":
                check_from(req, resp, fails)
            elif op == "interval":
                check_interval(req, resp, fails)
            elif op == "roundTo":
                if "Z" in req:
                    check_zonotope_hull("roundTo", req, resp, fails)
                else:
                    check_round_to_mat(req, resp, fails)
            elif op in EXACT_HULLS:
                check_zonotope_hull(op, req, resp, fails)
            else:
                continue
            checked += 1
        except Exception as e:  # a malformed pair is itself a finding, not a crash
            fails.append(f"id {req.get('id')}: {op}: exception during check: {e}")
    print(f"check_sound: checked {checked} response(s) against {len(req_lines)} request(s)")
    if fails:
        print(f"check_sound: {len(fails)} FAILURE(S):")
        for f_ in fails:
            print(f"  {f_}")
        return 1
    print("check_sound: all checked responses are sound")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())


# --------------------------------------------  END OF CODE  ------------------------------------ #
