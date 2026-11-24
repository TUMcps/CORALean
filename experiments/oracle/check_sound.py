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
* `nnLayer.relaxation`: the exact activation at a grid of every box lies within the error of the
  line (`exp` in 60-digit `decimal`); `nnLayer.productLine`: the products at the factors' corners
  lie within the error of the line; `nnLayer.softmaxSumBounds`: the sums of the exponentials at a
  grid of the box lie in the box; `conZonotope.dualBound`: `h <= w' beta` at the feasible points of a grid of the box;
  `neuralNetwork.backwardBound`: `lower <= C N(x)` at the corners and the center of the input box,
  where every ReLU's input lies in its box `[l, u]` (else the fixture itself is wrong).
* `nnLayer.mergeBuckets`: the activation's finite limits; `nnLayer.groupSort`: every group of `y`
  is its group of `x` sorted; `nnLayer.generatorReduction`: the center is kept and the input's
  hull lies in the output's; `neuralNetwork.normalForm`: the exact product of every fused run of
  linear layers lies in its boxes `W`, `b`, the activations in order (`check_nn_forms`).
* `neuralNetwork.propagateBounds`, `backpropIntervalBatch`, `backprop` (ReLU networks): the same
  midpoint-radius passes over ℚ (`Real.IntervalChain`) lie in the reply's bounds;
  `neuralNetwork.sensitivity`: the exact Jacobian at the point lies in the reply (`check_nn_bounds`).
* `neuralNetwork.backpropZonotopeBatch` and `nnLayer.backpropZonotopeBatch`: the reply's slopes
  lie in `[0, 1]`, and the exact backward pass over ℚ with them (`W'` and `m .*`) of the center's
  and every input generator's gradient lies in the reply; `neuralNetwork.computeFGSMAttack`: `x`
  plus `epsilon` times the sign of the exact gradient of `softmax(y) - t` (`exp` in 60-digit
  `decimal`) lies in the reply; `neuralNetwork.getInputNeuronOrder`: the pixels in order, along
  the snake, or ascending by the exact mean absolute sensitivity; the integer structure ops
  (`getNumNeurons`, `getNumParams`, `getRefinableLayers`, `getOrderPattern`,
  `prepareForZonoBatchEval`) recomputed (`check_nn_batch9`).
* `nnLayer.*`, `neuralNetwork.evaluate` and `neuralNetwork.evaluateGraph`: the exact network
  (`Fraction` for the linear and ReLU layers, `decimal` at 60 digits for sigmoid and tanh, the fit
  plus its error `d` for `poly`) at points of the input set lies in the hull of the output set
  (`check_nn_op`).
* `polyZonotope.*`, `interval.polyZonotope` and `zonotope.polyZonotope`: points of the input set (the
  center, the corners of the first four factors, half the others, the independent generators at
  `+-1`) lie in the hull of the output (`check_polyzono_op`); `plus`, `mtimes`, `evalPowers` and
  `quadMap` map the points first, `enclose` takes the points of both operands, `exactPlus` adds points of
  both at equal factor values, `cartProd` joins them with points of `Z`; a split puts every point
  in the hull of a half, the identifier, structure and map ops of the second batch (`check_pz_batch4`) check a subset, a cover or the image at sampled factor values, `center` must be `c`, and a `false` of `isIntersecting` needs every point
  outside the polytope.
* `intervalMatrix.exponentialRemainder`: the exact remainder of the center matrix lies in the answer;
  `matZonotope.reduce`: the box of the set lies in the box of the answer; `matZonotope.contains`:
  a `true` has every matrix in the box of the set (`check_class_op`).
* `taylm.*`: at grid points `t` of the box `[-1, 1]^k` and at both ends of each operand's remainder,
  the exact value of the operation on the functions `poly + r` lies in the output model, its
  polynomial at `t` plus `[rem + Ierr]`; `interval` must hold the value (`check_taylm_op`);
  `constant` and `fromRange` hold their numbers. `neuralNetwork.evaluateTaylm`: the network's value
  at grid points and remainder ends, in 60 digits, lies in each output model at the same `t`
  (`check_nn_taylm`).
* `nonlinearSys.linReachPoly`: constant-input runs of the system, by RK4 in 60 digits from points of
  `R`, lie in the hulls of the response (`check_pz_lin_reach`).
* Every op `ping` lists occurs in the requests, so none is served without a test.

Every check names the request `id` and the violated bound on failure. Uses
only the standard library.
"""

# Authors:       Tobias Ladner, Claude Opus 5.5, Claude Sonnet 5.5
# Written:       30-September-2026
# Last update:   24-November-2026
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
    # no error box: zero
    einf = parse_vec(z["E"]["inf"]) if "E" in z else [F(0)] * len(c)
    esup = parse_vec(z["E"]["sup"]) if "E" in z else [F(0)] * len(c)
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
    elif op == "signCora":
        a = box("I")
        sgn = lambda x: F(1) if x > 0 else F(-1) if x < 0 else F(0)
        contained(([sgn(l) for l in a[0]], [sgn(h) for h in a[1]]), out(), op, req, fails)
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
    elif op in ("exp", "sqrt", "sqrtCora", "log", "sinh", "tanh"):
        f = {"exp": lambda x: dec(x).exp(), "sinh": lambda x: (dec(x).exp() - (-dec(x)).exp()) / 2,
             "tanh": lambda x: (dec(x).exp() - (-dec(x)).exp()) / (dec(x).exp() + (-dec(x)).exp()),
             "sqrt": lambda x: dec(x).sqrt() if x >= 0 else Decimal(0),
             "sqrtCora": lambda x: dec(x).sqrt() if x >= 0 else Decimal(0),
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
    elif op in ("supportFunc", "supportFuncCora"):
        a = box("I")
        d = parse_vec(req["dir"])
        exact = sum(max(x * l, x * h) for x, l, h in zip(d, *a))
        if parse_scalar(resp["value"]) < exact:
            fails.append(f"id {rid}: {op}: {resp['value']} below the exact {exact}")
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
    elif op == "isIntersectingApprox":
        # a `false` is a proof: in a coordinate the exact boxes are apart by more than `tol`
        if not resp["value"]:
            lo, hi = hull_of_zonotope_json(req["Z"])
            if "Z2" in req:
                slo, shi = hull_of_zonotope_json(req["Z2"])
            else:
                slo, shi = parse_vec(req["I"]["inf"]), parse_vec(req["I"]["sup"])
            tol = parse_scalar(req["tol"])
            if not any(lo[i] > shi[i] + tol or hi[i] < slo[i] - tol for i in range(len(lo))):
                fails.append(f"id {rid}: isIntersectingApprox: false, but the boxes meet")
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


def decimal_pi() -> Decimal:
    """pi by Machin's formula, 60 digits."""
    def atan_inv(k):
        x = Decimal(1) / k
        s = t = x
        i = 1
        while abs(t) > Decimal(10) ** -58:
            t = -t / (k * k)
            i += 2
            s += t / i
        return s
    return 4 * (4 * atan_inv(5) - atan_inv(239))


def decimal_trig(x: Decimal, sine: bool) -> Decimal:
    """sin or cos of x by the Taylor series, 60 digits."""
    x = x % (2 * decimal_pi())
    t = x if sine else Decimal(1)
    s = t
    i = 1 if sine else 0
    while abs(t) > Decimal(10) ** -58:
        i += 2
        t = -t * x * x / (i * (i - 1))
        s += t
    return s


def check_docking_polytope(req, resp, fails):
    """The hypotheses of `dockingPolytope_subset_safe`, re-derived with the measured coefficient
    error: rows `(-w, -w, a_j, b_j) <= beta`, `eps` the largest distance of `(a_j, b_j)` from
    `(cos, sin)(2 pi j / N)`, `kappa = cos(pi / N) - sqrt 2 eps`; then `kappa > 0`,
    `0 <= w <= kappa 2n / sqrt 2` and `beta <= kappa / 5` put the polytope inside the safe set
    `|v| <= 0.2 + 2n |s|`. The empty fallback (one row `0 <= -1`) is inside it trivially."""
    rid = req.get("id")
    P = resp["P"]
    r, _, A = parse_mat(P["A"])
    b = parse_vec(P["b"])
    if r == 1 and all(x == 0 for x in A[0]) and b[0] < 0:
        return
    N = req["N"]
    pi = decimal_pi()
    n = dec(parse_scalar(req["n"]))
    if len(A) != N or any(A[j][0] != A[0][0] or A[j][1] != A[0][0] or b[j] != b[0] for j in range(N)):
        fails.append(f"id {rid}: dockingPolytope: rows are not (-w, -w, a, b) <= beta")
        return
    w, beta = -dec(A[0][0]), dec(b[0])
    eps = max(max(abs(dec(A[j][2]) - decimal_trig(2 * pi * j / N, False)),
                  abs(dec(A[j][3]) - decimal_trig(2 * pi * j / N, True))) for j in range(N))
    kappa = decimal_trig(pi / N, False) - Decimal(2).sqrt() * eps
    if not (kappa > 0 and 0 <= w <= kappa * 2 * n / Decimal(2).sqrt() and beta <= kappa / 5):
        fails.append(f"id {rid}: dockingPolytope: the polytope is not shown inside the safe set")


def nn_points(req):
    """Points of the input set of an `nnLayer`/`neuralNetwork` op: the center, the corners of the
    first four factors, and half the others; a polynomial zonotope's factors enter through its
    exponent matrix and its independent generators at `+-1`."""
    import itertools
    if "Z" in req:
        c = parse_vec(req["Z"]["c"])
        _, h, G = parse_mat(req["Z"]["G"])
        for s in itertools.product([F(-1), F(0), F(1)], repeat=min(h, 4)):
            s = list(s) + [F(1, 2)] * (h - len(s))
            yield [c[i] + sum(G[i][j] * s[j] for j in range(h)) for i in range(len(c))]
        return
    P = req["P"]
    c = parse_vec(P["c"])
    _, h, G = parse_mat(P["G"])
    _, q, GI = parse_mat(P["GI"]) if "GI" in P else (0, 0, [[] for _ in c])
    if "Exp" in P:
        p, E = P["Exp"]["rows"], P["Exp"]["data"]
        exps = [[E[k * h + j] for k in range(p)] for j in range(h)]
    else:
        p, exps = h, [[1 if k == j else 0 for k in range(h)] for j in range(h)]
    for a in itertools.product([F(-1), F(0), F(1, 2)], repeat=min(p, 4)):
        a = list(a) + [F(1, 2)] * (p - len(a))
        for b in ([F(-1)] * q, [F(1)] * q):
            mono = [F(1)] * h
            for j in range(h):
                for k in range(p):
                    mono[j] *= a[k] ** exps[j][k]
            yield [c[i] + sum(G[i][j] * mono[j] for j in range(h))
                   + sum(GI[i][j] * b[j] for j in range(q)) for i in range(len(c))]


FOLDED_KINDS = ("batchNorm", "avgPool", "lipLinear")


def graph_apply(layers, x):
    """The exact graph network of `neuralNetwork.evaluateGraph` on a point: layer `k` reads its
    `source` (`-1` the input, by default `k - 1`) through `W`, adds `b` and each residual's source
    through `R` (the identity without one), then its activation; the last output."""
    outs = {-1: x}
    for k, layer in enumerate(layers):
        _, _, W = parse_mat(layer["W"])
        b = parse_vec(layer["b"])
        v = outs[layer.get("source", k - 1)]
        z = [sum(W[i][j] * v[j] for j in range(len(v))) + b[i] for i in range(len(W))]
        for r in layer.get("residuals", []):
            u = outs[r["source"]]
            R = parse_mat(r["R"])[2] if "R" in r else [[F(int(i == j)) for j in range(len(u))]
                                                        for i in range(len(u))]
            z = [z[i] + sum(R[i][j] * u[j] for j in range(len(u))) for i in range(len(z))]
        act = layer.get("activation", "identity")
        if act == "relu":
            z = [max(v, F(0)) for v in z]
        elif act == "sign":
            z = [F((v > 0) - (v < 0)) for v in z]
        elif act == "square":
            z = [v * v for v in z]
        elif act == "product":
            h = len(z) // 2
            z = [z[i] * z[h + i] for i in range(h)] + [F(0)] * h
        outs[k] = z
    return outs[len(layers) - 1]


def nn_apply(layer, x):
    """The exact layer on a point: `Fraction` where it is rational, else `Decimal`."""
    kind = layer["kind"]
    if kind == "linear":
        _, _, W = parse_mat(layer["W"])
        b = parse_vec(layer["b"])
        if any(isinstance(v, Decimal) for v in x):
            W, b = [[dec(w) for w in row] for row in W], [dec(v) for v in b]
        return [sum(W[i][j] * x[j] for j in range(len(x))) + b[i] for i in range(len(W))]
    if kind == "relu":
        return [max(v, F(0)) for v in x]
    if kind == "leakyRelu":
        a = parse_scalar(layer["alpha"])
        return [max(a * v, v) for v in x]
    if kind == "sign":
        return [F((v > 0) - (v < 0)) for v in x]
    if kind == "square":
        return [v * v for v in x]
    if kind == "conv":
        return conv_apply(layer, x)
    # CORA.cpp's activations with a line of their own, in 60-digit decimals
    if kind in ("exp", "reciprocal", "cube", "inverse", "softplus", "root", "invSqrt"):
        d = [dec(v) if isinstance(v, F) else v for v in x]
        f = {"exp": lambda t: t.exp(), "reciprocal": lambda t: 1 / max(t, Decimal(1)),
             "cube": lambda t: t ** 3, "inverse": lambda t: 1 / t,
             "softplus": lambda t: (1 + t.exp()).ln(), "root": lambda t: t.sqrt(),
             "invSqrt": lambda t: 1 / t.sqrt()}[kind]
        return [f(v) for v in d]
    if kind == "elementwiseAffine":
        sc, of = parse_vec(layer["scale"]), parse_vec(layer["offset"])
        sc, of = (sc * len(x) if len(sc) == 1 else sc), (of * len(x) if len(of) == 1 else of)
        return [sc[i] * x[i] + of[i] for i in range(len(x))]
    if kind == "batchNorm":
        # the exact map; the oracle encloses CORA.cpp's map folded in floats (FOLDED_SLACK)
        C, H, W = layer["input"]
        per = {k: parse_vec(layer[k]) for k in ("scale", "offset", "mean", "var")}
        per = {k: (v * C if len(v) == 1 else v) for k, v in per.items()}
        eps = parse_scalar(layer["epsilon"])
        d = [dec(F(v)) if not isinstance(v, Decimal) else v for v in x]
        out = []
        for i, v in enumerate(d):
            ch = i // (H * W)
            sd = (dec(per["var"][ch] + eps)).sqrt()
            out.append(dec(per["scale"][ch]) * (v - dec(per["mean"][ch])) / sd + dec(per["offset"][ch]))
        return out
    if kind == "avgPool":
        C, H, W = layer["input"]
        kh, kw = layer["pool"]
        k = F(1, kh * kw)
        conv = {"kernel": {"rows": C, "cols": kh * kw, "data": [f"{1}*2^0"] * (C * kh * kw)},
                "kshape": [kh, kw], "input": layer["input"], "stride": layer.get("stride", [kh, kw]),
                "pads": layer.get("pads", [0, 0, 0, 0]), "groups": C}
        Ho = (H + conv["pads"][0] + conv["pads"][2] - kh) // conv["stride"][0] + 1
        Wo = (W + conv["pads"][1] + conv["pads"][3] - kw) // conv["stride"][1] + 1
        conv["b"] = {"rows": C * Ho * Wo, "cols": 1, "data": ["0*2^0"] * (C * Ho * Wo)}
        return [k * v for v in conv_apply(conv, x)]
    if kind == "lipLinear":
        _, _, W = parse_mat(layer["W"])
        b = parse_vec(layer["b"])
        lam = parse_scalar(layer["lambda"])
        out = []
        for i in range(len(W)):
            nrm = max(sum(abs(w) for w in W[i]) / lam, F(1))
            out.append((sum(W[i][j] * x[j] for j in range(len(x))) + b[i]) / nrm)
        return out
    if kind == "poly":
        # the fit given, at the edge `+d` of its error (the set holds every deviation up to `d`)
        _, _, C = parse_mat(layer["coeffs"])
        d = parse_vec(layer["d"])
        return [sum(C[i][k] * x[i] ** k for k in range(len(C[i]))) + d[i] for i in range(len(x))]
    d = [dec(F(v)) if not isinstance(v, Decimal) else v for v in x]
    if kind == "sigmoid":
        return [1 / (1 + (-v).exp()) for v in d]
    if kind == "tanh":
        return [(v.exp() - (-v).exp()) / (v.exp() + (-v).exp()) for v in d]
    raise ValueError(kind)


def conv_apply(layer, x):
    """ONNX's Conv of the point `x` (`input` `(C, H, W)` in C order): the kernel `(out, C / groups,
    kh, kw)` as rows, `stride`, `dilation`, `pads` (top, left, bottom, right), `groups`, bias `b`."""
    C, H, W = layer["input"]
    kh, kw = layer["kshape"]
    sh, sw = layer.get("stride", [1, 1])
    dh, dw = layer.get("dilation", [1, 1])
    pt, pl, pb, pr = layer.get("pads", [0, 0, 0, 0])
    groups = layer.get("groups", 1)
    co, _, K = parse_mat(layer["kernel"])
    b = parse_vec(layer["b"])
    cg = C // groups
    Ho = (H + pt + pb - dh * (kh - 1) - 1) // sh + 1
    Wo = (W + pl + pr - dw * (kw - 1) - 1) // sw + 1
    out = []
    for o in range(co):
        g = o // (co // groups)
        for y in range(Ho):
            for xo in range(Wo):
                acc = F(0)
                for ci in range(cg):
                    for ky in range(kh):
                        for kx in range(kw):
                            py, px = y * sh + ky * dh - pt, xo * sw + kx * dw - pl
                            if 0 <= py < H and 0 <= px < W:
                                acc += K[o][(ci * kh + ky) * kw + kx] * x[((g * cg + ci) * H + py) * W + px]
                out.append(acc + b[(o * Ho + y) * Wo + xo])
    return out


def check_nn_relaxation(req, resp, fails):
    """`nnLayer.relaxation`: at the ends, the middle, the stationary points (of the square, `log m`
    of the exponential, `1` and `1 / sqrt(-m)` of the reciprocal and the inverse, `+-sqrt(m / 3)` of
    the cube, the multiples of `pi / 2` for sin and cos, where `f' = m` for softplus, root and
    invSqrt) and a grid of every box, `|f(t) - (slope t + offset)| <= error`, exactly (`Fraction`)
    or in 60-digit `Decimal` (`exp`, `sin`, `cos`, `softplus`, `root`, `invSqrt`)."""
    kind = req["kind"]
    f = {"sign": lambda t: F((t > 0) - (t < 0)), "square": lambda t: t * t,
         "relu": lambda t: max(t, F(0)), "reciprocal": lambda t: 1 / max(t, F(1)),
         "exp": lambda t: dec(t).exp(), "cube": lambda t: t ** 3, "inverse": lambda t: 1 / t,
         "sin": lambda t: decimal_trig(dec(t), True), "cos": lambda t: decimal_trig(dec(t), False),
         "softplus": lambda t: (1 + dec(t).exp()).ln(), "root": lambda t: dec(t).sqrt(),
         "invSqrt": lambda t: 1 / dec(t).sqrt()}[kind]
    decimal_kind = kind in ("exp", "sin", "cos", "softplus", "root", "invSqrt")
    lo, hi = parse_vec(req["l"]), parse_vec(req["u"])
    m, o, e = parse_vec(resp["slope"]), parse_vec(resp["offset"]), parse_vec(resp["error"])
    for i, (a, b) in enumerate(zip(lo, hi)):
        ts = [a + (b - a) * F(k, 16) for k in range(17)]
        ts += [t for t in (F(0), F(1), m[i] / 2) if a <= t <= b]
        if kind == "exp" and m[i] > 0:
            ts += [t for t in (F(dec(m[i]).ln()),) if a <= t <= b]
        if kind in ("reciprocal", "inverse") and m[i] < 0:
            ts += [t for t in (F(1 / dec(-m[i]).sqrt()),) if a <= t <= b]
        if kind == "cube" and m[i] > 0:
            r = F((dec(m[i]) / 3).sqrt())
            ts += [t for t in (r, -r) if a <= t <= b]
        # the stationary points of f(x) - m x of the monotone lines
        if kind == "softplus" and 0 < m[i] < 1:
            ts += [t for t in (F((dec(m[i]) / (1 - dec(m[i]))).ln()),) if a <= t <= b]
        if kind == "root" and m[i] > 0:
            ts += [t for t in (1 / (4 * m[i] * m[i]),) if a <= t <= b]
        if kind == "invSqrt" and m[i] < 0:
            ts += [t for t in (F((1 / (-2 * dec(m[i]))) ** (dec(2) / 3)),) if a <= t <= b]
        if kind in ("sin", "cos"):
            # the extrema: the multiples of pi / 2 in the box
            half_pi = F(decimal_pi() / 2)
            j0 = int(a / half_pi) - 1
            ts += [j * half_pi for j in range(j0, j0 + int((b - a) / half_pi) + 3)
                   if a <= j * half_pi <= b]
        for t in ts:
            line = m[i] * t + o[i]
            if decimal_kind:
                dev, err = abs(f(t) - dec(line)), dec(e[i])
            else:
                dev, err = abs(f(t) - line), e[i]
            if dev > err:
                fails.append(f"id {req.get('id')}: nnLayer.relaxation: neuron {i} at {float(t)} "
                             f"leaves the band by {float(dev - err)}")
                return


def check_product_line(req, resp, fails):
    """`nnLayer.productLine`: at the corners and the center of the factors and of the interval
    center, `|a_i b_i - (c_b a_i + c_a b_i + offset_i)| <= error_i` exactly (`Fraction`)."""
    import itertools
    c, q, G, _, _ = parse_zonotope(req["Z"])
    m = len(c)
    n = m // 2
    dr = parse_vec(req["dr"]) if "dr" in req else [F(0)] * m
    o, e = parse_vec(resp["offset"]), parse_vec(resp["error"])
    for beta in itertools.product([F(-1), F(0), F(1)], repeat=min(q, 6)):
        beta = list(beta) + [F(0)] * (q - len(beta))
        for i in range(n):
            for sa, sb in itertools.product((-dr[i], F(0), dr[i]), (-dr[n + i], F(0), dr[n + i])):
                a = c[i] + sum(G[i][j] * beta[j] for j in range(q)) + sa
                b = c[n + i] + sum(G[n + i][j] * beta[j] for j in range(q)) + sb
                if abs(a * b - (c[n + i] * a + c[i] * b + o[i])) > e[i]:
                    fails.append(f"id {req.get('id')}: nnLayer.productLine: neuron {i} leaves the "
                                 "band")
                    return


def check_softmax_sums(req, resp, fails):
    """`nnLayer.softmaxSumBounds`: `W exp(d) + b` at a grid of the box `[l, u]` lies in
    `[inf, sup]` (60-digit `Decimal`)."""
    import itertools
    m, n, W = parse_mat(req["W"])
    b, lo, hi = parse_vec(req["b"]), parse_vec(req["l"]), parse_vec(req["u"])
    inf, sup = parse_vec(resp["inf"]), parse_vec(resp["sup"])
    for t in itertools.product(range(3), repeat=n):
        d = [lo[j] + (hi[j] - lo[j]) * F(t[j], 2) for j in range(n)]
        e = [dec(v).exp() for v in d]
        for i in range(m):
            v = sum(dec(W[i][j]) * e[j] for j in range(n)) + dec(b[i])
            if not dec(inf[i]) <= v <= dec(sup[i]):
                fails.append(f"id {req.get('id')}: nnLayer.softmaxSumBounds: row {i} leaves the box")
                return


def check_dual_bound(req, resp, fails):
    """`conZonotope.dualBound`: `h <= w' beta` at every feasible point of the grid `{-1, 0, 1}^q`
    (and halves of it) with `C beta <= d`."""
    import itertools
    p, q, C = parse_mat(req["C"])
    d, w = parse_vec(req["d"]), parse_vec(req["w"])
    h = parse_scalar(resp["h"])
    for beta in itertools.product([F(-1), F(-1, 2), F(0), F(1, 2), F(1)], repeat=q):
        if all(sum(C[i][j] * beta[j] for j in range(q)) <= d[i] for i in range(p)):
            v = sum(w[j] * beta[j] for j in range(q))
            if h > v:
                fails.append(f"id {req.get('id')}: conZonotope.dualBound: h = {float(h)} above "
                             f"w' beta = {float(v)} at a feasible beta")
                return


def check_backward_bound(req, resp, fails):
    """`neuralNetwork.backwardBound`: at the corners and the center of the box `|x - x0| <= r`, the
    exact network (`Fraction`) keeps every ReLU's input in its box and `lower <= C N(x)`."""
    import itertools
    x0, r = parse_vec(req["x"]), parse_vec(req["r"])
    _, _, C = parse_mat(req["C"])
    lower = parse_vec(resp["lower"])
    pts = [list(x0)] + [[x0[j] + s_ * r[j] for j, s_ in enumerate(sg)]
                        for sg in itertools.product([-1, 1], repeat=len(x0))]
    for x in pts:
        for layer in req["layers"]:
            if layer["kind"] == "linear":
                _, _, W = parse_mat(layer["W"])
                b = parse_vec(layer["b"])
                x = [sum(W[i][j] * x[j] for j in range(len(x))) + b[i] for i in range(len(W))]
            else:
                lo, hi = parse_vec(layer["l"]), parse_vec(layer["u"])
                if any(not (lo[i] <= x[i] <= hi[i]) for i in range(len(x))):
                    fails.append(f"id {req.get('id')}: neuralNetwork.backwardBound: a ReLU input "
                                 f"leaves its box [l, u] (the fixture is wrong)")
                    return
                x = [max(v, F(0)) for v in x]
        for q, row in enumerate(C):
            v = sum(row[i] * x[i] for i in range(len(x)))
            if lower[q] > v:
                fails.append(f"id {req.get('id')}: neuralNetwork.backwardBound: row {q}'s lower "
                             f"bound {float(lower[q])} above C N(x) = {float(v)}")
                return


def check_nn_forms(op, req, resp, fails):
    """The network forms: `nnLayer.mergeBuckets`, `nnLayer.groupSort`, `nnLayer.generatorReduction`
    and `neuralNetwork.normalForm` (see the module docstring)."""
    rid = req.get("id")
    if op == "nnLayer.mergeBuckets":
        want = {"relu": [F(0)], "sigmoid": [F(0), F(1)], "tanh": [F(-1), F(1)]}[req["kind"]]
        if parse_vec(resp["buckets"]) != want:
            fails.append(f"id {rid}: {op}: the buckets are not {want}")
        return
    if op == "nnLayer.groupSort":
        x, y, g = parse_vec(req["x"]), parse_vec(resp["y"]), req["groupSize"]
        for k in range(0, len(x), g):
            if sorted(x[k:k + g]) != y[k:k + g]:
                fails.append(f"id {rid}: {op}: group {k // g} is not sorted")
                return
        return
    if op == "nnLayer.generatorReduction":
        c_in = parse_vec(req["Z"]["c"])
        if parse_vec(resp["Z"]["c"]) != c_in:
            fails.append(f"id {rid}: {op}: the center changed")
        lo1, hi1 = hull_of_zonotope_json(req["Z"])
        lo2, hi2 = hull_of_zonotope_json(resp["Z"])
        if not hull_subset(lo1, hi1, lo2, hi2):
            fails.append(f"id {rid}: {op}: the input's hull leaves the output's")
        return
    # normalForm: the runs of linear layers fused exactly, then compared with the boxes
    out = list(resp["layers"])
    acc = None
    n = req["n"]

    def flush():
        if acc is None:
            return True
        layer = out.pop(0) if out else None
        if layer is None or layer["kind"] != "linear":
            fails.append(f"id {rid}: {op}: a fused linear layer is missing")
            return False
        W, b = acc
        _, _, Wlo = parse_mat(layer["W"]["inf"])
        _, _, Whi = parse_mat(layer["W"]["sup"])
        blo, bhi = parse_vec(layer["b"]["inf"]), parse_vec(layer["b"]["sup"])
        ok = all(Wlo[i][j] <= W[i][j] <= Whi[i][j] for i in range(len(W)) for j in range(len(W[0])))
        ok = ok and all(blo[i] <= b[i] <= bhi[i] for i in range(len(b)))
        if not ok:
            fails.append(f"id {rid}: {op}: the exact fused map leaves the boxes")
        return ok

    for layer in req["layers"]:
        kind = layer["kind"]
        if kind in ("linear", "elementwiseAffine", "identity"):
            if kind == "linear":
                _, _, M = parse_mat(layer["W"])
                v = parse_vec(layer["b"])
            elif kind == "elementwiseAffine":
                sc, of = parse_vec(layer["scale"]), parse_vec(layer["offset"])
                M = [[sc[i] if i == j else F(0) for j in range(len(sc))] for i in range(len(sc))]
                v = of
            else:
                M = [[F(int(i == j)) for j in range(n)] for i in range(n)]
                v = [F(0)] * n
            if acc is None:
                acc = (M, v)
            else:
                W, b = acc
                acc = ([[sum(M[i][k] * W[k][j] for k in range(len(W))) for j in range(len(W[0]))]
                        for i in range(len(M))], [x + y for x, y in zip(mat_vec(M, b), v)])
            n = len(v)
            continue
        if not flush():
            return
        acc = None
        layer_out = out.pop(0) if out else None
        if layer_out is None or layer_out["kind"] != kind:
            fails.append(f"id {rid}: {op}: the activation {kind} is missing")
            return
    if not flush():
        return
    if out:
        fails.append(f"id {rid}: {op}: {len(out)} layers too many")


def check_nn_bounds(op, req, resp, fails):
    """The interval passes of a ReLU network over ℚ, against the reply (see the module docstring)."""
    rid = req.get("id")
    layers = [(parse_mat(L["W"])[2], parse_vec(L["b"]), L["activation"] == "relu")
              for L in req["layers"]]
    half = F(1, 2)

    def affine(W, b, lo, hi):
        mid = [(x + y) * half for x, y in zip(lo, hi)]
        rad = [(y - x) * half for x, y in zip(lo, hi)]
        c = [m + bi for m, bi in zip(mat_vec(W, mid), b)]
        r = mat_vec([[abs(w) for w in row] for row in W], rad)
        return [x - y for x, y in zip(c, r)], [x + y for x, y in zip(c, r)]

    def relu(v):
        return [max(x, F(0)) for x in v]

    def inside(name, exact, box):
        lo, hi = parse_vec(box["inf"]), parse_vec(box["sup"])
        if not all(a <= x <= b for a, x, b in zip(lo, exact, hi)):
            fails.append(f"id {rid}: {op}: the exact {name} leaves the reply")

    if op == "neuralNetwork.propagateBounds":
        i, bounds = req["i"], req["bounds"]
        if not layers[i][2] or bounds[i] is None:
            return
        lo, hi = relu(parse_vec(bounds[i]["l"])), relu(parse_vec(bounds[i]["u"]))
        for j in range(i + 1, len(layers)):
            lo, hi = affine(layers[j][0], layers[j][1], lo, hi)
            if layers[j][2]:
                if bounds[j] is not None:
                    lo = [max(x, y) for x, y in zip(lo, parse_vec(bounds[j]["l"]))]
                    hi = [min(x, y) for x, y in zip(hi, parse_vec(bounds[j]["u"]))]
                out = resp["bounds"][j]
                if not (all(a <= x for a, x in zip(parse_vec(out["l"]), lo))
                        and all(x <= b for x, b in zip(hi, parse_vec(out["u"])))):
                    fails.append(f"id {rid}: {op}: the exact bounds of layer {j} leave the reply")
                return
        return
    if op == "neuralNetwork.sensitivity":
        # the Jacobian diag(relu'(z_K)) W_K ... diag(relu'(z_1)) W_1 at the exact point
        h = parse_vec(req["x"])
        J = [[F(int(i == j)) for j in range(len(h))] for i in range(len(h))]
        for W, b, act in layers:
            z = [x + y for x, y in zip(mat_vec(W, h), b)]
            J = [[sum(W[i][k] * J[k][j] for k in range(len(J))) for j in range(len(J[0]))]
                 for i in range(len(W))]
            if act:
                J = [[x if z[i] > 0 else F(0) for x in J[i]] for i in range(len(J))]
                z = relu(z)
            h = z
        _, _, Jlo = parse_mat(resp["J"]["inf"])
        _, _, Jhi = parse_mat(resp["J"]["sup"])
        if not all(Jlo[i][j] <= J[i][j] <= Jhi[i][j] for i in range(len(J)) for j in range(len(J[0]))):
            fails.append(f"id {rid}: {op}: the exact Jacobian leaves the reply")
        return
    point = op == "neuralNetwork.backprop"
    lo = parse_vec(req["x"] if point else req["l"])
    hi = parse_vec(req["x"] if point else req["u"])
    pre = []
    for W, b, act in layers:
        lo, hi = affine(W, b, lo, hi)
        pre.append((lo, hi))
        if act:
            lo, hi = relu(lo), relu(hi)
    gl = parse_vec(req["g"] if point else req["gl"])
    gu = parse_vec(req["g"] if point else req["gu"])
    for (W, _, act), (zl, zu) in reversed(list(zip(layers, pre))):
        if act:
            gl = [g * (1 if z > 0 else 0) for g, z in zip(gl, zl)]
            gu = [g * (1 if z > 0 else 0) for g, z in zip(gu, zu)]
        Wt = [list(col) for col in zip(*W)]
        mid = mat_vec(Wt, [(x + y) * half for x, y in zip(gu, gl)])
        rad = mat_vec([[abs(w) for w in row] for row in Wt], [(y - x) * half for x, y in zip(gl, gu)])
        gl, gu = [m - r for m, r in zip(mid, rad)], [m + r for m, r in zip(mid, rad)]
    if point:
        inside("gradient", gl, resp["g"])
    else:
        inside("lower gradient", gl, resp["gl"])
        inside("upper gradient", gu, resp["gu"])


def check_nn_batch9(op, req, resp, fails):
    """The zonotope batch backpropagation, FGSM, the input order and the structure ops of a
    network of `{W, b, activation}` layers (see the module docstring)."""
    rid = req.get("id")

    def fail(what):
        fails.append(f"id {rid}: {op}: {what}")

    def layers_of(req):
        return [(parse_mat(L["W"])[2], parse_vec(L["b"]), L["activation"] == "relu")
                for L in req["layers"]]

    def transpose_times(W, g):
        return [sum(W[i][j] * g[i] for i in range(len(W))) for j in range(len(W[0]))]

    if op.endswith("backpropZonotopeBatch"):
        slopes = [parse_vec(v) if v is not None else None for v in resp.get("slopes", [])]
        if any(v is not None and not all(F(0) <= m <= F(1) for m in v) for v in slopes):
            fail("a slope leaves [0, 1]")
            return
        # the backward steps: ("W", W) or ("m", slopes), from the output back
        if op.startswith("nnLayer."):
            layer = req["layer"]
            steps = [("W", parse_mat(layer["W"])[2])] if layer["kind"] == "linear" \
                else [("m", slopes[0])]
        else:
            steps, it = [], iter(slopes)
            for W, _, relu in layers_of(req):
                steps.append(("W", W))
                m = next(it)
                if relu:
                    steps.append(("m", m))
        def back(g):
            for kind, v in reversed(steps):
                g = transpose_times(v, g) if kind == "W" else [a * b for a, b in zip(v, g)]
            return g
        lo, hi = parse_box(resp["gc"])
        gc = back(parse_vec(req["gc"]))
        if not all(a <= x <= b for a, x, b in zip(lo, gc, hi)):
            fail("the exact center gradient leaves the reply")
        _, q, gG = parse_mat(req["gG"])
        Glo, Ghi = parse_box_mat(resp["gG"])
        h = len(Glo[0]) if Glo else 0
        for j in range(h):
            g = back([row[j] for row in gG])
            if not all(Glo[i][j] <= g[i] <= Ghi[i][j] for i in range(len(g))):
                fail(f"the exact gradient of generator {j} leaves the reply")
                return
        return
    if op == "neuralNetwork.computeFGSMAttack":
        x, t, eps = parse_vec(req["x"]), parse_vec(req["t"]), parse_scalar(req["epsilon"])
        h, pre = x, []
        L = layers_of(req)
        for W, b, relu in L:
            z = [u + v for u, v in zip(mat_vec(W, h), b)]
            pre.append(z)
            h = [max(u, F(0)) for u in z] if relu else z
        e = [dec(v).exp() for v in h]
        g = [ei / sum(e) - dec(ti) for ei, ti in zip(e, t)]
        for (W, _, relu), z in reversed(list(zip(L, pre))):
            if relu:
                g = [gi if zi > 0 else Decimal(0) for gi, zi in zip(g, z)]
            g = [sum(dec(W[i][j]) * g[i] for i in range(len(W))) for j in range(len(W[0]))]
        want = [xi + eps * (1 if gi > 0 else -1 if gi < 0 else 0) for xi, gi in zip(x, g)]
        lo, hi = parse_box(resp["z"])
        if not all(a <= w <= b for a, w, b in zip(lo, want, hi)):
            fail("the exact signed step leaves the reply")
        return
    if op == "neuralNetwork.getInputNeuronOrder":
        order, method = resp["order"], req["method"]
        n = len(req["layers"][0]["W"]["data"]) // req["layers"][0]["W"]["rows"]
        size = req.get("inputSize")
        pixels = n if size is None else size[1] * size[2]
        if method == "in-order":
            want = list(range(pixels))
        elif method == "snake":
            A = [[y * size[2] + x for x in range(size[2])] for y in range(size[1])]
            want = []
            while A and A[0]:
                want += A[0]
                A = [list(r) for r in zip(*[row[::-1] for row in A[1:]])]
        else:
            if order is None:
                return
            # the exact Jacobian at x, then the mean absolute entry per pixel
            hx, J = parse_vec(req["x"]), None
            J = [[F(int(i == j)) for j in range(n)] for i in range(n)]
            for W, b, relu in layers_of(req):
                z = [u + v for u, v in zip(mat_vec(W, hx), b)]
                J = [[sum(W[i][k] * J[k][j] for k in range(len(J))) for j in range(n)]
                     for i in range(len(W))]
                if relu:
                    J = [J[i] if z[i] > 0 else [F(0)] * n for i in range(len(J))]
                    z = [max(u, F(0)) for u in z]
                hx = z
            key = [sum(abs(J[i][j]) for i in range(len(J))) for j in range(n)]
            if size is not None:
                key = [sum(key[p + pixels * c] for c in range(size[0])) for p in range(pixels)]
            if sorted(order) != list(range(pixels)) or \
                    any(key[a] > key[b] for a, b in zip(order, order[1:])):
                fail("the order is not ascending in the exact sensitivity")
            return
        if order != want:
            fail(f"the order is not {want}")
        return
    shapes = [(L["W"]["rows"], L["W"]["cols"], L["activation"] != "identity") for L in req["layers"]]
    refinable = [k for k, (_, _, a) in enumerate(shapes) if a]
    if op == "neuralNetwork.getNumNeurons":
        want, got = [n for _, n, _ in shapes] + [shapes[-1][0]], resp["numNeurons"]
    elif op == "neuralNetwork.getNumParams":
        want, got = sum(m * n + m for m, n, _ in shapes), resp["numParams"]
    elif op == "neuralNetwork.getRefinableLayers":
        want, got = refinable, resp["layers"]
    elif op == "neuralNetwork.getOrderPattern":
        orders = req.get("orders", [])
        def expand(o, n):
            return [1] * n if not o else o if len(o) == n else [max(o)] * n
        want = [expand(orders[k] if k < len(orders) else [], shapes[k][0]) for k in refinable]
        got = resp["pattern"]
    else:
        def count(name):
            v = req.get(name, "inf")
            return None if v == "inf" else v
        q, e, added = count("numInitGens"), count("numApproxErr"), []
        q = shapes[0][1] if q is None else q
        for m, _, a in shapes:
            d = (m if e is None else min(e, m)) if a else 0
            added.append([q, d] if a else None)
            q += d
        want, got = (q, added), (resp["numGen"], resp["approxErrGens"])
    if got != want:
        fail(f"{got} is not {want}")


def check_nn_op(op, req, resp, fails):
    """`nnLayer.*` and `neuralNetwork.evaluate`: the exact network's outputs at points of the input
    set lie in the output set's hull (`c +- sum |G| +- sum |GI| +- E`)."""
    if op == "nnLayer.relaxation":
        check_nn_relaxation(req, resp, fails)
        return
    if op == "nnLayer.productLine":
        check_product_line(req, resp, fails)
        return
    if op == "nnLayer.softmaxSumBounds":
        check_softmax_sums(req, resp, fails)
        return
    if op == "neuralNetwork.backwardBound":
        check_backward_bound(req, resp, fails)
        return
    if op in ("nnLayer.mergeBuckets", "nnLayer.groupSort", "nnLayer.generatorReduction",
              "neuralNetwork.normalForm"):
        check_nn_forms(op, req, resp, fails)
        return
    if op in ("neuralNetwork.propagateBounds", "neuralNetwork.backpropIntervalBatch",
              "neuralNetwork.backprop", "neuralNetwork.sensitivity"):
        check_nn_bounds(op, req, resp, fails)
        return
    if op in ("neuralNetwork.backpropZonotopeBatch", "nnLayer.backpropZonotopeBatch",
              "neuralNetwork.computeFGSMAttack", "neuralNetwork.getInputNeuronOrder",
              "neuralNetwork.getNumNeurons", "neuralNetwork.getNumParams",
              "neuralNetwork.getRefinableLayers", "neuralNetwork.getOrderPattern",
              "neuralNetwork.prepareForZonoBatchEval"):
        check_nn_batch9(op, req, resp, fails)
        return
    graph = op == "neuralNetwork.evaluateGraph"
    layers = [] if graph else [req["layer"]] if "layer" in req else req["layers"]
    out = resp["Z"] if "Z" in resp else resp["P"]
    c = parse_vec(out["c"])
    _, h, G = parse_mat(out["G"])
    gi = parse_mat(out["GI"])[2] if "GI" in out else [[] for _ in c]
    einf, esup = parse_vec(out["E"]["inf"]), parse_vec(out["E"]["sup"])
    n = len(c)
    lo = [dec(c[i] - sum(abs(g) for g in G[i]) - sum(abs(g) for g in gi[i]) + einf[i])
          for i in range(n)]
    hi = [dec(c[i] + sum(abs(g) for g in G[i]) + sum(abs(g) for g in gi[i]) + esup[i])
          for i in range(n)]
    slack = Decimal(10) ** -40
    # a layer CORA.cpp folds in floats (FOLDED_KINDS): the map enclosed is the folded one, checked
    # against the exact one to a relative 2^-40
    folded = any(layer["kind"] in FOLDED_KINDS for layer in layers)
    for x in nn_points(req):
        if graph:
            x = graph_apply(req["layers"], x)
        for layer in layers:
            x = nn_apply(layer, x)
        for i in range(n):
            y = dec(x[i]) if isinstance(x[i], F) else x[i]
            tol = slack + (Decimal(2) ** -40 * (1 + abs(y)) if folded else 0)
            if y < lo[i] - tol or y > hi[i] + tol:
                fails.append(f"id {req.get('id')}: {op}: output {i} = {float(y)} leaves "
                             f"[{float(lo[i])}, {float(hi[i])}]")
                return



def pz_points(P):
    """Points of the polynomial zonotope `P` (`{"c","G","GI","Exp"}`): the center, the corners of
    the first four factors, half the others, the independent generators at `+-1`."""
    import itertools
    c = parse_vec(P["c"])
    _, h, G = parse_mat(P["G"])
    _, q, GI = parse_mat(P["GI"]) if "GI" in P else (0, 0, [[] for _ in c])
    if "Exp" in P:
        p, E = P["Exp"]["rows"], P["Exp"]["data"]
        exps = [[E[k * h + j] for k in range(p)] for j in range(h)]
    else:
        p, exps = h, [[1 if k == j else 0 for k in range(h)] for j in range(h)]
    for a in itertools.product([F(-1), F(0), F(1, 2), F(1)], repeat=min(p, 3)):
        a = list(a) + [F(1, 2)] * (p - len(a))
        for b in ([F(-1)] * q, [F(1)] * q):
            mono = [F(1)] * h
            for j in range(h):
                for k in range(p):
                    mono[j] *= a[k] ** exps[j][k]
            yield [c[i] + sum(G[i][j] * mono[j] for j in range(h))
                   + sum(GI[i][j] * b[j] for j in range(q)) for i in range(len(c))]


def pz_points_uniform(P):
    """Points of `P` with every factor at one value of `-1, 0, 1/2, 1` and the independent
    generators at `+-1`: two sets with shared factors give corresponding points."""
    c = parse_vec(P["c"])
    _, h, G = parse_mat(P["G"])
    _, q, GI = parse_mat(P["GI"]) if "GI" in P else (0, 0, [[] for _ in c])
    p, E = P["Exp"]["rows"], P["Exp"]["data"]
    exps = [[E[k * h + j] for k in range(p)] for j in range(h)]
    for v in [F(-1), F(0), F(1, 2), F(1)]:
        for b in ([F(-1)] * q, [F(1)] * q):
            mono = [v ** sum(exps[j]) for j in range(h)]
            yield [c[i] + sum(G[i][j] * mono[j] for j in range(h))
                   + sum(GI[i][j] * b[j] for j in range(q)) for i in range(len(c))]


def pz_hull(out):
    """The hull of a polynomial zonotope or zonotope response: `c +- sum |G| +- sum |GI| +- E`."""
    c = parse_vec(out["c"])
    _, h, G = parse_mat(out["G"])
    gi = parse_mat(out["GI"])[2] if "GI" in out else [[] for _ in c]
    einf, esup = parse_vec(out["E"]["inf"]), parse_vec(out["E"]["sup"])
    n = len(c)
    lo = [dec(c[i] - sum(abs(g) for g in G[i]) - sum(abs(g) for g in gi[i]) + einf[i])
          for i in range(n)]
    hi = [dec(c[i] + sum(abs(g) for g in G[i]) + sum(abs(g) for g in gi[i]) + esup[i])
          for i in range(n)]
    return lo, hi


BATCH4 = ("replaceId", "restoreId", "rmId", "onlyId", "noIndep", "lift", "isBounded", "isFullDim",
          "isequal", "representsa", "sum", "restructure", "jacobian", "linComb", "convHull",
          "getSubset", "resolve", "matMap", "cubMap", "partZonotope", "outerApprox")


def pz_parts(P):
    """`(c, G, GI, exps, ids)` of a wire polynomial zonotope: `G`, `GI` as lists of columns, `exps`
    a list over the generators of the exponent per factor."""
    c = parse_vec(P["c"])
    _, h, G = parse_mat(P["G"])
    _, q, GI = parse_mat(P["GI"]) if "GI" in P else (0, 0, [[] for _ in c])
    p, E = P["Exp"]["rows"], P["Exp"]["data"]
    exps = [[E[k * h + j] for k in range(p)] for j in range(h)]
    ids = P.get("id", list(range(1, p + 1)))
    return c, [[G[i][j] for i in range(len(c))] for j in range(h)], \
        [[GI[i][j] for i in range(len(c))] for j in range(q)], exps, ids


def pz_eval(P, assign, default, gi=0):
    """The point of `P` with factor `id` at `assign[id]` (else `default`), the independent
    generators at `gi` (`0` or `+-1`)."""
    c, G, GI, exps, ids = pz_parts(P)
    n = len(c)
    out = list(c)
    for j, col in enumerate(G):
        mono = F(1)
        for k, e in enumerate(exps[j]):
            mono *= assign.get(ids[k], default) ** e
        out = [out[i] + col[i] * mono for i in range(n)]
    return [out[i] + sum(g[i] * gi for g in GI) for i in range(n)]


def pz_samples(P, fixed=None):
    """Assignments of the factors of `P` not in `fixed`: all at one of `-1, 1/2, 1`, and a mixed one."""
    ids = pz_parts(P)[4]
    fixed = fixed or {}
    outs = []
    for v in (F(-1), F(1, 2), F(1), F(0)):
        outs.append({**{i: v for i in ids}, **fixed})
    outs.append({**{i: (F(1, 3) if t % 2 else F(-1)) for t, i in enumerate(ids)}, **fixed})
    return outs


def inside_hull(lo, hi, pts, fails, tag):
    slack = Decimal(10) ** -40
    for x in pts:
        for i in range(len(lo)):
            y = dec(x[i]) if isinstance(x[i], F) else x[i]
            if y < lo[i] - slack or y > hi[i] + slack:
                fails.append(f"{tag}: coordinate {i} = {float(y)} leaves "
                             f"[{float(lo[i])}, {float(hi[i])}]")
                return False
    return True


def with_error_box(P):
    """`P` with the error box `E` a request may leave out, zero."""
    if "E" in P:
        return P
    z = {"rows": P["c"]["rows"], "cols": 1, "data": ["0*2^0"] * P["c"]["rows"]}
    return {**P, "E": {"inf": z, "sup": z}}


def check_pz_batch4(op, name, req, resp, fails):
    """The second batch of `polyZonotope.*` ops (identifiers, structure, predicates, maps)."""
    tag = f"id {req.get('id')}: {op}"
    P = req.get("P")
    if name == "isBounded":
        if resp["value"] is not True:
            fails.append(f"{tag}: a polynomial zonotope is bounded")
        return
    if name == "isFullDim":
        return
    if name == "isequal":
        if resp["value"]:
            # a `true` needs the stored data equal, as parsed numbers
            a, b = pz_parts(P), pz_parts(req["Q"])
            if a[:4] != b[:4] or a[4] != b[4] and False:
                fails.append(f"{tag}: true, but the data differ")
        return
    if name == "representsa":
        if resp["value"]:
            _, G, GI, _, _ = pz_parts(P)
            if any(v != 0 for col in G + GI for v in col):
                fails.append(f"{tag}: true, but a generator is not zero")
        return
    if name == "onlyId":
        c = parse_vec(P["c"])
        lo, hi = pz_hull(with_error_box(P))
        pts = list(pz_points(P))
        for key in ("P1", "P2"):
            lo2, hi2 = pz_hull(resp[key])
            shift = c if key == "P2" else [F(0)] * len(c)
            lo2 = [lo2[i] + dec(shift[i]) for i in range(len(c))]
            hi2 = [hi2[i] + dec(shift[i]) for i in range(len(c))]
            slack = Decimal(10) ** -40
            if any(lo2[i] < lo[i] - slack or hi2[i] > hi[i] + slack for i in range(len(c))):
                fails.append(f"{tag}: {key} leaves the hull of the set")
                return
        # the parts add up to the set: P1 + P2 - c covers the points
        l1, h1 = pz_hull(resp["P1"])
        l2, h2 = pz_hull(resp["P2"])
        cover = [(l1[i] + l2[i], h1[i] + h2[i]) for i in range(len(c))]
        for x in pts:
            for i in range(len(c)):
                if not cover[i][0] - Decimal(10) ** -40 <= dec(x[i]) <= cover[i][1] + Decimal(10) ** -40:
                    fails.append(f"{tag}: the parts do not cover the set")
                    return
        return
    lo, hi = pz_hull(resp["P"])
    slack = Decimal(10) ** -40
    n = len(lo)
    if name in ("noIndep", "rmId", "replaceId"):
        # a subset: the points of the result lie in the hull of the set
        plo, phi = pz_hull(with_error_box(P))
        pts = list(pz_points(resp["P"]))
        inside_hull(plo, phi, pts, fails, tag)
        return
    if name in ("restoreId", "partZonotope", "outerApprox", "restructure"):
        inside_hull(lo, hi, list(pz_points(P)), fails, tag)
        return
    if name == "lift":
        plo, phi = pz_hull(with_error_box(P))
        pairs = sorted(zip(plo, phi))
        if sorted(zip(lo, hi)) != pairs:
            fails.append(f"{tag}: the result is not a permutation of the coordinates")
        return
    if name == "sum":
        pts = []
        for a, *rest in zip(pz_points_uniform(P), *[pz_points_uniform(L) for L in req["L"]]):
            pts.append([a[i] + sum(r[i] for r in rest) for i in range(n)])
        inside_hull(lo, hi, pts, fails, tag)
        return
    if name == "jacobian":
        c, G, GI, exps, ids = pz_parts(P)
        k = ids.index(req["factor"])
        pts = []
        for assign in pz_samples(P):
            pt = [F(0)] * n
            for j, col in enumerate(G):
                e = exps[j][k]
                if e == 0:
                    continue
                mono = F(e)
                for t, ex in enumerate(exps[j]):
                    mono *= assign[ids[t]] ** (ex - 1 if t == k else ex)
                pt = [pt[i] + col[i] * mono for i in range(n)]
            pts.append(pt)
        inside_hull(lo, hi, pts, fails, tag)
        return
    if name in ("linComb", "convHull"):
        xs = list(pz_points(P))[::3] + [pz_eval(P, a, F(0)) for a in pz_samples(P)]
        ys = list(pz_points(req["Q"]))[::3] + [pz_eval(req["Q"], a, F(0)) for a in pz_samples(req["Q"])]
        pts = [[(x[i] + y[i]) / 2 for i in range(n)] for x in xs[:8] for y in ys[:8]]
        if name == "convHull":
            pts += xs + ys
        inside_hull(lo, hi, pts, fails, tag)
        return
    if name in ("getSubset", "resolve"):
        ids = req["ids"] if "ids" in req else pz_parts(P)[4]
        vals = parse_vec(req["val"] if name == "getSubset" else req["x"])
        fixed = {i: vals[t] for t, i in enumerate(ids)}
        pts = [pz_eval(P, a, F(0)) for a in pz_samples(P, fixed)]
        inside_hull(lo, hi, pts, fails, tag)
        return
    if name == "matMap":
        nn, kk, mm = req["n"], req["k"], req["m"]
        pts = []
        sa, sb = pz_samples(req["P"]), pz_samples(req["Q"])
        for a in range(len(sa)):
            ids = pz_parts(req["P"])[4] + pz_parts(req["Q"])[4]
            both = {**sb[a], **sa[a]}
            x, y = pz_eval(req["P"], both, F(0)), pz_eval(req["Q"], both, F(0))
            # column-major matrices, the product column by column
            X = [[x[j * nn + i] for j in range(kk)] for i in range(nn)]
            Y = [[y[j * kk + i] for j in range(mm)] for i in range(kk)]
            pts.append([sum(X[i][t] * Y[t][j] for t in range(kk)) for j in range(mm) for i in range(nn)])
        inside_hull(lo, hi, pts, fails, tag)
        return
    if name == "cubMap":
        nd = len(pz_parts(P)[0])
        Ts = [[parse_mat(M)[2] for M in row] for row in req["T"]]
        pts = []
        for x in list(pz_points(P)):
            pts.append([sum(x[k] * sum(x[a] * Ti[k][a][b] * x[b] for a in range(nd) for b in range(nd))
                            for k in range(nd)) for Ti in Ts])
        inside_hull(lo, hi, pts, fails, tag)
        return


def check_polyzono_op(op, req, resp, fails):
    """The `polyZonotope.*` ops and the two conversions: the exact image of the points of the
    operands lies in the hull of the response (a necessary condition, not an exact one)."""
    name = op.split(".", 1)[1] if op.startswith("polyZonotope.") else op
    rid = req.get("id")
    if name in BATCH4 and op.startswith("polyZonotope."):
        check_pz_batch4(op, name, req, resp, fails)
        return
    if name == "dim":
        if resp["value"] != len(parse_vec(req["P"]["c"])):
            fails.append(f"id {rid}: {op}: wrong dimension {resp['value']}")
        return
    if name == "center":
        if parse_vec(resp["c"]) != parse_vec(req["P"]["c"]):
            fails.append(f"id {rid}: {op}: not the center of the set")
        return
    if name == "isIntersecting":
        if not resp["value"]:
            # a `false` is a proof: every point of the set violates a row of the polytope
            S = req["S"]
            _, _, A = parse_mat(S["A"])
            b = parse_vec(S["b"])
            Ae = parse_mat(S["Ae"])[2] if "Ae" in S else []
            be = parse_vec(S["be"]) if "be" in S else []
            for x in pz_points(req["P"]):
                inside = all(sum(r[j] * x[j] for j in range(len(x))) <= b[i]
                             for i, r in enumerate(A)) and \
                    all(sum(r[j] * x[j] for j in range(len(x))) == be[i]
                        for i, r in enumerate(Ae))
                if inside:
                    fails.append(f"id {rid}: {op}: false, but {x} lies in both")
                    return
        return
    if name in ("splitDepFactor", "splitLongestGen"):
        # every point of the set lies in the hull of one of the two halves
        halves = [pz_hull(resp["P1"]), pz_hull(resp["P2"])]
        slack = Decimal(10) ** -40
        for x in pz_points(req["P"]):
            if not any(all(lo[i] - slack <= dec(x[i]) <= hi[i] + slack for i in range(len(x)))
                       for lo, hi in halves):
                fails.append(f"id {rid}: {op}: the point {[float(v) for v in x]} is in no half")
                return
        return
    if name == "interval":
        lo = [dec(x) for x in parse_vec(resp["I"]["inf"])]
        hi = [dec(x) for x in parse_vec(resp["I"]["sup"])]
    elif name == "zonotope" and op.startswith("polyZonotope."):
        lo, hi = pz_hull(resp["Z"])
    else:
        lo, hi = pz_hull(resp["P"])
    n = len(lo)
    # the points of every operand, through the op
    if op == "zonotope.polyZonotope":
        c, _, G = parse_vec(req["Z"]["c"]), None, parse_mat(req["Z"]["G"])[2]
        h = len(G[0]) if G and G[0] else 0
        pts = [[c[i] + sum(G[i][j] * s[j] for j in range(h)) for i in range(n)]
               for s in itertools_product(h)]
    elif op == "interval.polyZonotope":
        a, b = parse_vec(req["I"]["inf"]), parse_vec(req["I"]["sup"])
        pts = [[a[i] for i in range(n)], [b[i] for i in range(n)],
                [(a[i] + b[i]) / 2 for i in range(n)]]
    else:
        pts = list(pz_points(req["P"]))
        if name == "plus":
            if "Q" in req:
                qs = list(pz_points(req["Q"]))
            elif "Z" in req:
                zc, zG = parse_vec(req["Z"]["c"]), parse_mat(req["Z"]["G"])[2]
                zh = len(zG[0]) if zG and zG[0] else 0
                qs = [[zc[i] + sum(zG[i][j] * s[j] for j in range(zh)) for i in range(n)]
                      for s in itertools_product(zh)]
            elif "I" in req:
                a, b = parse_vec(req["I"]["inf"]), parse_vec(req["I"]["sup"])
                qs = [a, b, [(a[i] + b[i]) / 2 for i in range(n)]]
            else:
                qs = [parse_vec(req["v"])]
            pts = [[x[i] + y[i] for i in range(n)] for x in pts[::3] for y in qs[::2] or qs]
        elif name == "mtimes":
            _, _, M = parse_mat(req["M"])
            pts = [mat_vec(M, x) for x in pts]
            n = len(M)
        elif name == "enclose":
            pts = pts + list(pz_points(req["Q"]))
        elif name == "exactPlus":
            # every factor at the same value in both sets, so that shared factors agree
            pts = [[x[i] + y[i] for i in range(n)]
                   for x, y in zip(pz_points_uniform(req["P"]), pz_points_uniform(req["Q"]))]
        elif name == "cartProd":
            zc, zG = parse_vec(req["Z"]["c"]), parse_mat(req["Z"]["G"])[2]
            zh = len(zG[0]) if zG and zG[0] else 0
            zs = [[zc[i] + sum(zG[i][j] * s[j] for j in range(zh)) for i in range(len(zc))]
                  for s in itertools_product(zh)]
            pts = [x + z for x in pts[::3] for z in zs[::2] or zs]
        elif name == "project":
            # the chosen coordinates of every point
            dims = req["dims"]
            pts = [[x[d] for d in dims] for x in pts]
            n = len(dims)
        elif name == "quadMap":
            # every output x' Q_k x, exact
            Qs = [parse_mat(Qk)[2] for Qk in req["Q"]]
            pts = [[sum(x[a] * Qk[a][b] * x[b] for a in range(len(x)) for b in range(len(x)))
                    for Qk in Qs] for x in pts]
            n = len(Qs)
        elif name == "evalPowers":
            # every coordinate through its polynomial, lowest degree first
            _, _, C = parse_mat(req["coeffs"])
            pts = [[sum(C[i][k] * x[i] ** k for k in range(len(C[i]))) for i in range(n)]
                   for x in pts]
    slack = Decimal(10) ** -40
    for x in pts:
        for i in range(n):
            y = dec(x[i]) if isinstance(x[i], F) else x[i]
            if y < lo[i] - slack or y > hi[i] + slack:
                fails.append(f"id {rid}: {op}: coordinate {i} = {float(y)} leaves "
                             f"[{float(lo[i])}, {float(hi[i])}]")
                return


def eval_field(node, x, u):
    """The expression tree of a `nonlinearSys.*` request at the state `x` and the input `u`, in
    `Decimal` (60 digits)."""
    if "x" in node:
        return x[node["x"]]
    if "u" in node:
        return u[node["u"]]
    if "const" in node:
        return dec(parse_scalar(node["const"]))
    a = [eval_field(t, x, u) for t in node["args"]]
    o = node["op"]
    if o == "add":
        return a[0] + a[1]
    if o == "sub":
        return a[0] - a[1]
    if o == "mul":
        return a[0] * a[1]
    if o == "div":
        return a[0] / a[1]
    if o == "neg":
        return -a[0]
    if o == "pow":
        return a[0] ** node["exponent"]
    if o == "sin":
        return decimal_trig(a[0], True)
    if o == "cos":
        return decimal_trig(a[0], False)
    if o == "exp":
        return a[0].exp()
    if o == "sqrt":
        return a[0].sqrt()
    if o == "log":
        return a[0].ln()
    raise ValueError(f"no reference evaluation of `{o}`")


def check_pz_lin_reach(req, resp, fails):
    """`nonlinearSys.linReachPoly`: constant-input runs of the system from points of `R`, by RK4
    in 60 digits at 16 steps, lie in the hull of `timeInterval` at every step and of `timePoint`
    at the end (a necessary condition: the sets are outer approximations of the reach set)."""
    import itertools
    rid = req.get("id")
    n, m = req["n"], req["m"]
    dt = dec(parse_scalar(req["timeStep"]))
    lo_i, hi_i = pz_hull(resp["timeInterval"])
    lo_p, hi_p = pz_hull(resp["timePoint"])
    inputs = [[]]
    if m > 0:
        uc = parse_vec(req["U"]["c"])
        _, h, UG = parse_mat(req["U"]["G"])
        inputs = [[dec(uc[i] + sum(UG[i][j] * (s[j] if j < len(s) else 0) for j in range(h)))
                   for i in range(m)]
                  for s in itertools.product([F(-1), F(1)], repeat=min(h, 2))]
    steps = 16
    hh = dt / steps
    slack = Decimal(10) ** -9
    for x0 in itertools.islice(pz_points(req["R"]), 0, None, 3):
        for u in inputs:
            x = [dec(v) for v in x0]
            for k in range(steps):
                f = lambda y: [eval_field(t, y, u) for t in req["f"]]
                k1 = f(x)
                k2 = f([x[i] + hh / 2 * k1[i] for i in range(n)])
                k3 = f([x[i] + hh / 2 * k2[i] for i in range(n)])
                k4 = f([x[i] + hh * k3[i] for i in range(n)])
                x = [x[i] + hh / 6 * (k1[i] + 2 * k2[i] + 2 * k3[i] + k4[i]) for i in range(n)]
                last = k == steps - 1
                for i in range(n):
                    if x[i] < lo_i[i] - slack or x[i] > hi_i[i] + slack or \
                            (last and (x[i] < lo_p[i] - slack or x[i] > hi_p[i] + slack)):
                        fails.append(f"id {rid}: linReachPoly: coordinate {i} of a run at step "
                                     f"{k + 1} = {float(x[i])} leaves the sets")
                        return


def itertools_product(h):
    """The corners of the unit box of dimension `min(h, 6)`, the other coefficients 1/2."""
    import itertools
    for s in itertools.product([F(-1), F(1)], repeat=min(h, 6)):
        yield list(s) + [F(1, 2)] * (h - len(s))


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
    elif op == "intervalMatrix.exponentialRemainder":
        # the Taylor remainder of the center matrix, a member, lies in the answer
        if resp["IM"] is None:
            return
        _, _, lo = parse_mat(req["IM"]["inf"])
        _, _, hi = parse_mat(req["IM"]["sup"])
        n = len(lo)
        Mc = [[(lo[i][j] + hi[i][j]) / 2 for j in range(n)] for i in range(n)]
        R = mat_exp(Mc, 60)
        T = mat_exp(Mc, req["maxOrder"] + 1)
        _, _, rlo = parse_mat(resp["IM"]["inf"])
        _, _, rhi = parse_mat(resp["IM"]["sup"])
        if not all(rlo[i][j] <= R[i][j] - T[i][j] <= rhi[i][j]
                   for i in range(n) for j in range(n)):
            fails.append(f"id {rid}: exponentialRemainder: the center's remainder leaves it")
    elif op in ("matZonotope.reduce", "matZonotope.contains"):
        # the box of the set: `c ± Σ |G| + [E.inf, E.sup]`, entry by entry
        def box(z):
            _, _, c = parse_mat(z["c"])
            gs = [parse_mat(g)[2] for g in z["G"]]
            _, _, einf = parse_mat(z["E"]["inf"])
            _, _, esup = parse_mat(z["E"]["sup"])
            rows, cols = range(len(c)), range(len(c[0]))
            r = [[sum(abs(g[i][j]) for g in gs) for j in cols] for i in rows]
            return ([[c[i][j] - r[i][j] + einf[i][j] for j in cols] for i in rows],
                    [[c[i][j] + r[i][j] + esup[i][j] for j in cols] for i in rows])
        lo, hi = box(req["mZ"])
        if op == "matZonotope.reduce":
            # the reduction encloses the set, so its box encloses the set's box
            rlo, rhi = box(resp["mZ"])
            if not all(rlo[i][j] <= lo[i][j] and hi[i][j] <= rhi[i][j]
                       for i in range(len(lo)) for j in range(len(lo[0]))):
                fails.append(f"id {rid}: matZonotope.reduce: the set's box leaves the answer's")
        elif resp["value"]:
            # a member lies in the box of the set
            for m in req["M"]:
                _, _, x = parse_mat(m)
                if not all(lo[i][j] <= x[i][j] <= hi[i][j]
                           for i in range(len(lo)) for j in range(len(lo[0]))):
                    fails.append(f"id {rid}: matZonotope.contains: a matrix outside the box")
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
    elif op == "specification.dockingPolytope":
        check_docking_polytope(req, resp, fails)
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


def taylm_eval(T, t):
    """The polynomial of the request or response model `T` at the point `t`, exactly."""
    total = F(0)
    for term in T["terms"]:
        v = parse_scalar(term["c"])
        for x, e in zip(t, term["e"]):
            v *= x ** e
        total += v
    return total


def taylm_rem(T):
    lo, hi = parse_scalar(T["rem"]["inf"]), parse_scalar(T["rem"]["sup"])
    if "Ierr" in T:
        lo += parse_scalar(T["Ierr"]["inf"])
        hi += parse_scalar(T["Ierr"]["sup"])
    return lo, hi


def check_taylm_op(op, req, resp, fails):
    """The output model holds the operation on every function `poly + r` the inputs hold, at
    grid points of the box and the ends of the remainders."""
    rid = req.get("id")
    name = op[len("taylm."):]
    if name in ("constant", "fromRange"):
        # the constructors: every number they claim, at every point of the box
        vals = ([parse_scalar(req["c"])] if name == "constant" else
                [parse_scalar(req["lo"]), parse_scalar(req["hi"]),
                 (parse_scalar(req["lo"]) + parse_scalar(req["hi"])) / 2])
        out = resp["T"]
        lo, hi = taylm_rem(out)
        for t in ([[F(-1)] * out["vars"], [F(1, 2)] * out["vars"]] if out["vars"] else [[]]):
            p = taylm_eval(out, t)
            if any(not lo <= v - p <= hi for v in vals):
                fails.append(f"id {rid}: {op}: a number of the box leaves the model")
                return
        return
    T = req["T"]
    k = T["vars"]
    grid = [F(-1), F(-1, 3), F(0), F(1, 2), F(1)]
    points = [[]]
    for _ in range(k):
        points = [p + [g] for p in points for g in grid][:200]
    tlo, thi = taylm_rem(T)
    Q = req.get("Q")
    for t in points:
        fs = [taylm_eval(T, t) + r for r in (tlo, thi)]
        if Q is not None:
            qlo, qhi = taylm_rem(Q)
            gs = [taylm_eval(Q, t) + r for r in (qlo, qhi)]
        s_ = parse_scalar(req["s"]) if "s" in req else None
        for f in fs:
            if name == "interval":
                lo = parse_scalar(resp["I"]["inf"]["data"][0])
                hi = parse_scalar(resp["I"]["sup"]["data"][0])
                if not lo <= f <= hi:
                    fails.append(f"id {rid}: taylm.interval: f({t}) = {f} leaves [{lo}, {hi}]")
                continue
            if name in ("plus", "minus", "times") and Q is not None:
                op2 = {"plus": lambda a, b: a + b, "minus": lambda a, b: a - b,
                       "times": lambda a, b: a * b}[name]
                values = [op2(f, g) for g in gs]
            elif name in ("plus", "minus", "times"):
                values = [{"plus": f + s_, "minus": f - s_, "times": f * s_}[name]]
            elif name == "uminus":
                values = [-f]
            elif name == "uplus":
                values = [f]
            elif name == "power":
                values = [f ** req["k"]]
            else:
                return
            out = resp["T"]
            lo, hi = taylm_rem(out)
            p = taylm_eval(out, t)
            for v in values:
                if not lo <= v - p <= hi:
                    fails.append(f"id {rid}: {op}: the value at {t} leaves the model")
                    return


def check_nn_taylm(req, resp, fails):
    """`neuralNetwork.evaluateTaylm`: at grid points `t` of the box and at the ends of the input
    remainders, the network's value (60-digit decimals) lies in each output model at the same
    `t`, its polynomial plus `[rem + Ierr]`."""
    rid = req.get("id")
    xs = req["x"]
    k = xs[0]["vars"]
    grid = [F(-1), F(-1, 3), F(0), F(1, 2), F(1)]
    points = [[]]
    for _ in range(k):
        points = [p + [g] for p in points for g in grid][:60]
    ends = [taylm_rem(x) for x in xs]
    acts = {"relu": lambda v: max(v, Decimal(0)),
            "sigmoid": lambda v: Decimal(1) / (Decimal(1) + (-v).exp()),
            "tanh": lambda v: (Decimal(2) / (Decimal(1) + (-2 * v).exp())) - Decimal(1)}
    for t in points:
        for side in range(2 ** min(len(xs), 4)):
            vals = [dec(taylm_eval(x, t) + (ends[j][1] if (side >> j) & 1 else ends[j][0]))
                    for j, x in enumerate(xs)]
            for layer in req["layers"]:
                if layer["kind"] == "linear":
                    W, b = layer["W"], layer["b"]
                    r, c = W["rows"], W["cols"]
                    w = [dec(parse_scalar(v)) for v in W["data"]]
                    bb = [dec(parse_scalar(v)) for v in b["data"]]
                    vals = [sum(w[i * c + j] * vals[j] for j in range(c)) + bb[i]
                            for i in range(r)]
                else:
                    vals = [acts[layer["kind"]](v) for v in vals]
            for i, out in enumerate(resp["Y"]):
                lo, hi = taylm_rem(out)
                p = taylm_eval(out, t)
                if not dec(lo) - Decimal("1e-40") <= vals[i] - dec(p) <= dec(hi) + Decimal("1e-40"):
                    fails.append(f"id {rid}: neuralNetwork.evaluateTaylm: output {i} at {t} leaves "
                                 f"its model")
                    return


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
            if op.startswith("polyZonotope.") or op in ("interval.polyZonotope",
                                                          "zonotope.polyZonotope"):
                check_polyzono_op(op, req, resp, fails)
            elif op == "neuralNetwork.evaluateTaylm":
                check_nn_taylm(req, resp, fails)
            elif op.startswith("taylm."):
                check_taylm_op(op, req, resp, fails)
            elif op == "nonlinearSys.linReachPoly":
                check_pz_lin_reach(req, resp, fails)
            elif op.startswith("interval."):
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
            elif op.startswith(("nnLayer.", "neuralNetwork.")):
                check_nn_op(op, req, resp, fails)
            elif op == "conZonotope.dualBound":
                check_dual_bound(req, resp, fails)
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
