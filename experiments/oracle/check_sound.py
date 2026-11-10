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

* The ops of `Ops/IntervalOps.lean` and `Ops/ZonotopeMethods.lean` (`interval.<op>`,
  `zonotope.<op>`): where an exact value is computable over ℚ -- the box arithmetic, the
  projections, the support function, the norm, `exp`/`log`/`sqrt`/`sinh`/`tanh` through
  `decimal` at 60 digits -- the response must contain it (`CHECKS_INTERVAL`,
  `CHECKS_ZONOTOPE`); `minkDiff` is an inner approximation and is checked the other way round.
* Every op `ping` lists occurs in the requests, so none is served without a test.

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
from decimal import Decimal, getcontext
from fractions import Fraction as F

getcontext().prec = 60


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
    some point of its `toSet`, generator coefficients and the error box chosen independently
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
    """`linComb(Z,Z2)` (`Set.linComb`, not the convex hull): the coordinatewise union of the two
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



# --------------------------------  INTERVAL AND ZONOTOPE OPS  ------------------------------- #

def parse_box(b):
    """`{"inf","sup"}` of column vectors, as `(lo, hi)` lists. An empty box, `{"empty":true,"n":n}`
    or bounds without columns, is the library's `lo = 1 > 0 = hi` in each of its `n` coordinates."""
    if b.get("empty"):
        return [F(1)] * b["n"], [F(0)] * b["n"]
    if b["inf"].get("cols") == 0:
        return [F(1)] * b["inf"]["rows"], [F(0)] * b["inf"]["rows"]
    return parse_vec(b["inf"]), parse_vec(b["sup"])


def parse_box_mat(b):
    _, _, lo = parse_mat(b["inf"])
    _, _, hi = parse_mat(b["sup"])
    return lo, hi


def dec(x: F) -> Decimal:
    return Decimal(x.numerator) / Decimal(x.denominator)


PI = Decimal("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899")


def dec_floor_pole(x: F) -> int:
    """The index `k` of the branch `(k*pi - pi/2, k*pi + pi/2)` holding `x` (a pole is a boundary,
    which no float is at, to the 40 digits of `PI`)."""
    return int(((dec(x) + PI / 2) / PI).to_integral_value(rounding="ROUND_FLOOR"))


def dtan(x: F) -> Decimal:
    """`tan x` to about 40 digits, by the Taylor series of `sin` and `cos` after reducing `x`
    modulo `pi`."""
    k = dec_floor_pole(x)
    y = dec(x) - k * PI
    sin, cos, term_s, term_c = Decimal(0), Decimal(0), y, Decimal(1)
    for n in range(1, 120):
        cos += term_c
        sin += term_s
        term_c = -term_c * y * y / ((2 * n - 1) * (2 * n))
        term_s = -term_s * y * y / ((2 * n) * (2 * n + 1))
    return sin / cos


def contained(exact, out, label, req, fails, slack=Decimal(0)):
    """The exact box `(lo, hi)` lies inside the output box, coordinatewise; `slack` absorbs the
    rounding of the `decimal` reference values."""
    elo, ehi = exact
    olo, ohi = out
    for i in range(len(elo)):
        if elo[i] > ehi[i]:
            continue  # an empty exact result: nothing to enclose
        if dec(olo[i]) > dec(elo[i]) + slack or dec(ohi[i]) < dec(ehi[i]) - slack:
            fails.append(f"id {req.get('id')}: {label}: coordinate {i}: exact "
                         f"[{float(elo[i])}, {float(ehi[i])}] not inside output "
                         f"[{float(olo[i])}, {float(ohi[i])}]")


def zip2(f, a, b):
    return [f(x, y) for x, y in zip(a, b)]


def box_times(a, b):
    lo, hi = [], []
    for i in range(len(a[0])):
        l, h = interval_mul(a[0][i], a[1][i], b[0][i], b[1][i])
        lo.append(l)
        hi.append(h)
    return lo, hi


def box_abs(b):
    lo, hi = [], []
    for l, h in zip(*b):
        lo.append(F(0) if l <= 0 <= h else min(abs(l), abs(h)))
        hi.append(max(abs(l), abs(h)))
    return lo, hi


def box_power(b, k):
    lo, hi = [], []
    for l, h in zip(*b):
        cands = [l ** k, h ** k]
        if k % 2 == 0 and l <= 0 <= h:
            cands.append(F(0))
        lo.append(min(cands))
        hi.append(max(cands))
    return lo, hi


def box_mtimes(M, b):
    lo, hi = [], []
    for row in M:
        l = h = F(0)
        for m, bl, bh in zip(row, b[0], b[1]):
            pl, ph = interval_mul(m, m, bl, bh)
            l, h = l + pl, h + ph
        lo.append(l)
        hi.append(h)
    return lo, hi


def monotone(f, b):
    return [f(x) for x in b[0]], [f(x) for x in b[1]]


def check_interval_op(op, req, resp, fails):
    """`interval.<op>`: the response contains what the exact arithmetic gives."""
    rid = req.get("id")
    box = lambda key: parse_box(req[key])
    out = lambda: parse_box(resp["I"])
    if op in ("plus", "minus", "times", "and", "or", "convHull", "enclose", "min", "max"):
        if "inf" in req["I"] and len(req["I"]["inf"]["data"]) and req["I"]["inf"]["cols"] != 1:
            return  # the matrix `plus` is checked in `check_interval_matrix_op`
        a, b = box("I"), box("I2")
        exact = {
            "plus": (zip2(lambda x, y: x + y, a[0], b[0]), zip2(lambda x, y: x + y, a[1], b[1])),
            "minus": (zip2(lambda x, y: x - y, a[0], b[1]), zip2(lambda x, y: x - y, a[1], b[0])),
            "times": box_times(a, b),
            "and": (zip2(max, a[0], b[0]), zip2(min, a[1], b[1])),
            "or": (zip2(min, a[0], b[0]), zip2(max, a[1], b[1])),
            "convHull": (zip2(min, a[0], b[0]), zip2(max, a[1], b[1])),
            "enclose": (zip2(min, a[0], b[0]), zip2(max, a[1], b[1])),
            "min": (zip2(min, a[0], b[0]), zip2(min, a[1], b[1])),
            "max": (zip2(max, a[0], b[0]), zip2(max, a[1], b[1])),
        }[op]
        contained(exact, out(), op, req, fails)
    elif op == "minkDiff":
        a, b = box("I"), box("I2")
        elo, ehi = zip2(lambda x, y: x - y, a[0], b[0]), zip2(lambda x, y: x - y, a[1], b[1])
        olo, ohi = out()
        for i in range(len(elo)):
            if elo[i] <= ehi[i] and (olo[i] < elo[i] or ohi[i] > ehi[i]):
                fails.append(f"id {rid}: minkDiff: output [{olo[i]}, {ohi[i]}] not inside the "
                             f"exact difference [{elo[i]}, {ehi[i]}]")
    elif op in ("uminus", "uplus", "abs", "round", "reduce"):
        a = box("I")
        exact = {"uminus": ([-h for h in a[1]], [-l for l in a[0]]), "uplus": a,
                 "abs": box_abs(a), "reduce": a}.get(op)
        if exact is not None:
            contained(exact, out(), op, req, fails)
    elif op == "power":
        contained(box_power(box("I"), req["exponent"]), out(), op, req, fails)
    elif op == "enlarge":
        a, f = box("I"), parse_scalar(req["factor"])
        c = [(l + h) / 2 for l, h in zip(*a)]
        r = [(h - l) / 2 * f for l, h in zip(*a)]
        contained(([x - y for x, y in zip(c, r)], [x + y for x, y in zip(c, r)]), out(), op,
                  req, fails)
    elif op == "mtimes" and "inf" not in req["M"] and req["I"]["inf"]["cols"] == 1:
        _, _, M = parse_mat(req["M"])
        contained(box_mtimes(M, box("I")), out(), op, req, fails)
    elif op == "mtimes" and "inf" in req["M"] and req["I"]["inf"]["cols"] == 1:
        Mlo, Mhi = parse_box_mat(req["M"])
        a = box("I")
        lo, hi = [], []
        for rl, rh in zip(Mlo, Mhi):
            l = h = F(0)
            for ml, mh, bl, bh in zip(rl, rh, a[0], a[1]):
                pl, ph = interval_mul(ml, mh, bl, bh)
                l, h = l + pl, h + ph
            lo.append(l)
            hi.append(h)
        contained((lo, hi), out(), op, req, fails)
    elif op == "enclosePoints":
        _, _, P = parse_mat(req["points"])
        contained(([min(r) for r in P], [max(r) for r in P]), out(), op, req, fails)
    elif op == "mrdivide":
        a, d = box("I"), parse_scalar(req["d"])
        cands = [(l / d, h / d) for l, h in zip(*a)]
        contained(([min(c) for c in cands], [max(c) for c in cands]), out(), op, req, fails)
    elif op == "rdivide":
        a, b = box("I"), box("I2")
        if all(l > 0 for l in b[0]):
            contained(box_times(a, ([1 / h for h in b[1]], [1 / l for l in b[0]])), out(), op,
                      req, fails)
    elif op == "partition":
        a, k = box("I"), req["splits"]
        lo = [l + F(i) * (h - l) / k for (l, h), i in zip(zip(*a), req["ind"])]
        hi = [l + F(i + 1) * (h - l) / k for (l, h), i in zip(zip(*a), req["ind"])]
        contained((lo, hi), out(), op, req, fails)
    elif op == "sign":
        a = box("I")
        contained(([F(0) if l >= 0 else F(-1) for l in a[0]],
                   [F(0) if h <= 0 else F(1) for h in a[1]]), out(), op, req, fails)
    elif op == "project":
        a = box("I")
        contained(([a[0][d] for d in req["dims"]], [a[1][d] for d in req["dims"]]), out(), op,
                  req, fails)
    elif op == "cartProd":
        a, b = box("I"), box("I2")
        contained((a[0] + b[0], a[1] + b[1]), out(), op, req, fails)
    elif op == "projectHighDim":
        a, N = box("I"), req["N"]
        lo, hi = [F(0)] * N, [F(0)] * N
        for k, d in enumerate(req["dims"]):
            lo[d], hi[d] = a[0][k], a[1][k]
        contained((lo, hi), out(), op, req, fails)
    elif op == "zonotope":
        a = box("I")
        zlo, zhi = hull_of_zonotope_json(resp["Z"])
        contained(a, (zlo, zhi), op, req, fails)
    elif op in ("exp", "sqrt", "log", "sinh", "tanh"):
        f = {"exp": lambda x: dec(x).exp(), "sinh": lambda x: (dec(x).exp() - (-dec(x)).exp()) / 2,
             "tanh": lambda x: (dec(x).exp() - (-dec(x)).exp()) / (dec(x).exp() + (-dec(x)).exp()),
             "sqrt": lambda x: dec(x).sqrt() if x >= 0 else Decimal(0),
             "log": lambda x: dec(x).ln()}[op]
        a = box("I")
        if op == "log" and any(l <= 0 for l in a[0]):
            return
        olo, ohi = out()
        for i in range(len(olo)):
            flo, fhi = f(a[0][i]), f(a[1][i])
            if dec(olo[i]) > flo + Decimal("1e-40") or dec(ohi[i]) < fhi - Decimal("1e-40"):
                fails.append(f"id {rid}: {op}: coordinate {i}: image [{flo}, {fhi}] not inside "
                             f"[{float(olo[i])}, {float(ohi[i])}]")
    elif op == "tan":
        # a bound is a number or "-inf"/"inf"; a finite pair needs a range with no pole, and
        # then encloses the tangent at the two ends (tan increases between poles)
        a = box("I")
        olo = [x if x == "-inf" else parse_scalar(x) for x in resp["I"]["inf"]["data"]]
        ohi = [x if x == "inf" else parse_scalar(x) for x in resp["I"]["sup"]["data"]]
        for i in range(len(a[0])):
            l, u = a[0][i], a[1][i]
            pole_free = dec_floor_pole(l) == dec_floor_pole(u)
            if olo[i] != "-inf":
                if not pole_free or dec(olo[i]) > dtan(l) + Decimal("1e-30"):
                    fails.append(f"id {rid}: tan: coordinate {i}: finite lower bound "
                                 f"{float(olo[i])} for [{float(l)}, {float(u)}]")
            if ohi[i] != "inf":
                if not pole_free or dec(ohi[i]) < dtan(u) - Decimal("1e-30"):
                    fails.append(f"id {rid}: tan: coordinate {i}: finite upper bound "
                                 f"{float(ohi[i])} for [{float(l)}, {float(u)}]")
    elif op == "volume":
        a = box("I")
        v = F(1)
        for l, h in zip(*a):
            v *= max(h - l, F(0))
        if parse_scalar(resp["value"]) < v:
            fails.append(f"id {rid}: volume: {resp['value']} below the exact {v}")
    elif op == "rad":
        a = box("I")
        got = parse_vec(resp["value"])
        for i, (l, h) in enumerate(zip(*a)):
            if got[i] < (h - l) / 2:
                fails.append(f"id {rid}: rad: coordinate {i}: {got[i]} below {(h - l) / 2}")
    elif op in ("norm", "radius"):
        a = box("I")
        if op == "norm":
            exact = sum(max(abs(l), abs(h)) ** 2 for l, h in zip(*a))
            key = "normSq"
        else:
            exact = sum(((h - l) / 2) ** 2 for l, h in zip(*a))
            key = "radiusSq"
        if parse_scalar(resp[key]) < exact:
            fails.append(f"id {rid}: {op}: {resp[key]} below the exact {exact}")
    elif op == "supportFunc":
        a = box("I")
        d = parse_vec(req["dir"])
        exact = sum(max(x * l, x * h) for x, l, h in zip(d, *a))
        if parse_scalar(resp["value"]) < exact:
            fails.append(f"id {rid}: supportFunc: {resp['value']} below the exact {exact}")
    elif op in ("transpose", "ctranspose"):
        lo, hi = parse_box_mat(req["I"])
        olo, ohi = parse_box_mat(resp["I"])
        if [list(r) for r in zip(*lo)] != olo or [list(r) for r in zip(*hi)] != ohi:
            fails.append(f"id {rid}: {op}: not the transpose")
    elif op == "sum":
        lo, hi = parse_box_mat(req["I"])
        olo, ohi = parse_box_mat(resp["I"])
        axis = req["dim"]
        slo = [sum(c) for c in zip(*lo)] if axis == 1 else [sum(r) for r in lo]
        shi = [sum(c) for c in zip(*hi)] if axis == 1 else [sum(r) for r in hi]
        contained((slo, shi), ([r[0] for r in olo], [r[0] for r in ohi]), op, req, fails)


def zono_support(c, G, einf, esup, d):
    n, h = len(c), len(G[0]) if G else 0
    s = sum(d[i] * c[i] for i in range(n))
    s += sum(abs(sum(d[i] * G[i][j] for i in range(n))) for j in range(h))
    s += sum(max(d[i] * einf[i], d[i] * esup[i]) for i in range(n))
    return s


def particular_solution(G, p):
    """A `gamma` with `G gamma = p` over the rationals (free unknowns `0`), or `None` where there is
    none: Gaussian elimination on `[G | p]`."""
    n, h = len(G), len(G[0]) if G else 0
    A = [list(G[i]) + [p[i]] for i in range(n)]
    pivots, r = [], 0
    for col in range(h):
        piv = next((i for i in range(r, n) if A[i][col] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        A[r] = [x / A[r][col] for x in A[r]]
        for i in range(n):
            if i != r and A[i][col] != 0:
                f = A[i][col]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        pivots.append(col)
        r += 1
    if any(A[i][h] != 0 for i in range(r, n)):
        return None
    gamma = [F(0)] * h
    for k, col in enumerate(pivots):
        gamma[col] = A[k][h]
    return gamma


def check_zonotope_op(op, req, resp, fails):
    """`zonotope.<op>`: the response contains what the exact arithmetic gives."""
    rid = req.get("id")
    if op == "zonotopeNorm":
        # `inf` exactly where `p` is outside the span of the generators; otherwise a lower bound
        # on the norm, so at most the sup norm of any `gamma` reaching `p`
        _, _, G, _, _ = parse_zonotope(req["Z"])
        gamma = particular_solution(G, parse_vec(req["p"]))
        if resp["value"] == "inf":
            if gamma is not None:
                fails.append(f"id {rid}: zonotopeNorm: inf, but gamma = {gamma} reaches p")
        elif gamma is None:
            fails.append(f"id {rid}: zonotopeNorm: {resp['value']} for a p outside the span")
        elif parse_scalar(resp["value"]) > max([abs(g) for g in gamma] + [F(0)]):
            fails.append(f"id {rid}: zonotopeNorm: {resp['value']} above the norm of gamma = "
                         f"{gamma}")
    elif op == "cartProd":
        a = hull_of_zonotope_json(req["Z"])
        b = hull_of_zonotope_json(req["Z2"])
        contained((a[0] + b[0], a[1] + b[1]), hull_of_zonotope_json(resp["Z"]), op, req, fails)
    elif op in ("convHull", "enclose", "or"):
        check_zonotope_hull("linComb", req, resp, fails)
    elif op == "minkDiff":
        # inner: the difference plus the subtrahend lies in the minuend, so on the hulls
        # `lo' + lo2 >= lo` and `hi' + hi2 <= hi`; `null` (the check failed) claims nothing
        if resp["Z"] is not None:
            lo, hi = hull_of_zonotope_json(req["Z"])
            lo2, hi2 = hull_of_zonotope_json(req["Z2"])
            lo1, hi1 = hull_of_zonotope_json(resp["Z"])
            if not all(lo[i] <= lo1[i] + lo2[i] and hi1[i] + hi2[i] <= hi[i]
                       for i in range(len(lo))):
                fails.append(f"id {rid}: minkDiff: result plus subtrahend leaves the minuend")
    elif op == "reduceUnderApprox":
        # inner: the result lies in the input
        lo, hi = hull_of_zonotope_json(req["Z"])
        lo1, hi1 = hull_of_zonotope_json(resp["Z"])
        if not hull_subset(lo1, hi1, lo, hi):
            fails.append(f"id {rid}: reduceUnderApprox: result leaves the input")
    elif op == "project":
        a = hull_of_zonotope_json(req["Z"])
        contained(([a[0][d] for d in req["dims"]], [a[1][d] for d in req["dims"]]),
                  hull_of_zonotope_json(resp["Z"]), op, req, fails)
    elif op == "projectHighDim":
        a, N = hull_of_zonotope_json(req["Z"]), req["N"]
        lo, hi = [F(0)] * N, [F(0)] * N
        for k, d in enumerate(req["dims"]):
            lo[d], hi[d] = a[0][k], a[1][k]
        contained((lo, hi), hull_of_zonotope_json(resp["Z"]), op, req, fails)
    elif op == "box":
        contained(hull_of_zonotope_json(req["Z"]), parse_box(resp["I"]), op, req, fails)
    elif op == "supportFunc":
        c, _, G, einf, esup = parse_zonotope(req["Z"])
        exact = zono_support(c, G, einf, esup, parse_vec(req["dir"]))
        if parse_scalar(resp["value"]) < exact:
            fails.append(f"id {rid}: supportFunc: {resp['value']} below the exact {exact}")
    elif op == "norm":
        lo, hi = hull_of_zonotope_json(req["Z"])
        exact = sum(max(abs(l), abs(h)) ** 2 for l, h in zip(lo, hi))
        if parse_scalar(resp["normSq"]) < exact:
            fails.append(f"id {rid}: norm: {resp['normSq']} below the exact {exact}")
    elif op == "split":
        lo, hi = hull_of_zonotope_json(req["Z"])
        l1, h1 = hull_of_zonotope_json(resp["Z1"])
        l2, h2 = hull_of_zonotope_json(resp["Z2"])
        contained((lo, hi), (zip2(min, l1, l2), zip2(max, h1, h2)), op, req, fails)
    elif op in EXACT_HULLS:
        check_zonotope_hull(op, req, resp, fails)


# =======================================  MAIN DEFINITION  ===================================== #

def mat_exp(M, terms=40):
    """`exp(M)` by the exact Taylor sum over ℚ, `terms` terms: for the small matrices of the
    fixtures the tail is far below any rounding the oracle makes."""
    n = len(M)
    term = [[F(int(i == j)) for j in range(n)] for i in range(n)]
    total = [row[:] for row in term]
    for k in range(1, terms):
        term = [[sum(term[i][l] * M[l][j] for l in range(n)) / k for j in range(n)]
                for i in range(n)]
        total = [[total[i][j] + term[i][j] for j in range(n)] for i in range(n)]
    return total


def check_class_op(op, req, resp, fails):
    """The ops of the further classes this batch added."""
    rid = req.get("id")
    if op == "intervalMatrix.expmInd":
        # the exponential of the center matrix is a member, so it lies in the enclosure
        _, _, lo = parse_mat(req["IM"]["inf"])
        _, _, hi = parse_mat(req["IM"]["sup"])
        n = len(lo)
        E = mat_exp([[(lo[i][j] + hi[i][j]) / 2 for j in range(n)] for i in range(n)])
        _, _, rlo = parse_mat(resp["IM"]["inf"])
        _, _, rhi = parse_mat(resp["IM"]["sup"])
        if not all(rlo[i][j] <= E[i][j] <= rhi[i][j] for i in range(n) for j in range(n)):
            fails.append(f"id {rid}: expmInd: exp(center) leaves the enclosure")
    elif op in ("matZonotope.expm", "matZonotope.expmInd"):
        _, _, c = parse_mat(req["mZ"]["c"])
        n = len(c)
        E = mat_exp(c)
        gs = [parse_mat(g)[2] for g in resp["mZ"]["G"]]
        _, _, einf = parse_mat(resp["mZ"]["E"]["inf"])
        _, _, esup = parse_mat(resp["mZ"]["E"]["sup"])
        _, _, rc = parse_mat(resp["mZ"]["c"])
        for i in range(n):
            for j in range(n):
                r = sum(abs(g[i][j]) for g in gs)
                if not (rc[i][j] - r + einf[i][j] <= E[i][j] <= rc[i][j] + r + esup[i][j]):
                    fails.append(f"id {rid}: {op}: exp(center)[{i}][{j}] leaves the hull")
    elif op == "specification.check":
        # a `true` on a box against a box is a containment (safe set, invariant) or a
        # disjointness (unsafe set), checked exactly
        if resp["value"] and "inf" in req["set"] and "I" in req:
            slo, shi = parse_vec(req["set"]["inf"]), parse_vec(req["set"]["sup"])
            ilo, ihi = parse_vec(req["I"]["inf"]), parse_vec(req["I"]["sup"])
            if req["kind"] == "unsafeSet":
                ok = any(ihi[i] < slo[i] or shi[i] < ilo[i] for i in range(len(slo)))
            else:
                ok = hull_subset(ilo, ihi, slo, shi)
            if not ok:
                fails.append(f"id {rid}: specification.check: true, but the boxes disagree")
    elif op.startswith(("emptySet.representsa", "fullspace.representsa")):
        want = {"emptySet": op.startswith("emptySet"), "fullspace": op.startswith("fullspace")}
        t = req["type"]
        if t in want and resp["value"] != want[t]:
            fails.append(f"id {rid}: {op}: {t} answered {resp['value']}")
        if t in ("point", "origin") and resp["value"]:
            fails.append(f"id {rid}: {op}: {t} answered true")
    elif op == "fullspace.vertices":
        n, k = resp["V"]["rows"], resp["V"]["cols"]
        cols = {tuple(resp["V"]["data"][i * k + l] for i in range(n)) for l in range(k)}
        if k != 2 ** n or len(cols) != k:
            fails.append(f"id {rid}: fullspace.vertices: not the 2^{n} distinct corners")


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
    used_ops: set[str] = set()
    ping_ops: list[str] = []
    for rline, oline in zip(req_lines, resp_lines):
        try:
            req = json.loads(rline)
        except json.JSONDecodeError:
            continue  # the malformed-JSON regression line: nothing to check against
        resp = json.loads(oline)
        used_ops.add(req.get("op"))
        if not resp.get("ok"):
            continue  # an expected error: nothing exact to compare
        op = req.get("op")
        if op == "ping":
            ping_ops = resp.get("ops", [])
            continue
        try:
            if op.startswith("interval."):
                check_interval_op(op[len("interval."):], req, resp, fails)
            elif op.startswith("zonotope."):
                name = op[len("zonotope."):]
                if name == "plus" and "I" in req:
                    name = "plusBox"
                if name == "mtimes" and "inf" in req["M"]:
                    name = "mtimesInterval"
                if name in EXACT_HULLS:
                    check_zonotope_hull(name, req, resp, fails)
                else:
                    check_zonotope_op(name, req, resp, fails)
            elif op.startswith(("intervalMatrix.", "matZonotope.", "specification.",
                                "emptySet.", "fullspace.")):
                check_class_op(op, req, resp, fails)
            elif op == "from":
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
    for o in ping_ops:
        if o not in used_ops:
            fails.append(f"op `{o}` is listed by ping but no request uses it")
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
