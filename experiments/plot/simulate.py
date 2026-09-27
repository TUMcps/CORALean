#!/usr/bin/env python3
"""simulate.py -- exact trajectories of the headline spiral, for a plot overlay.

Standard library only. Reads one `experiments/config/headline_*.json`
(the same file `lake exe bench` reads) and writes one `.dat` file holding a
handful of trajectories from points of `X0`, under the *exact* closed-form
solution of `A = [[a, b], [-b, a]]`:

    e^{At} = e^{at} [[cos(bt), sin(bt)], [-sin(bt), cos(bt)]]

sampled only at the run's own sample times `t_k = k * dt`, `k = 0, ..., N`
(`N` the config's `steps`) -- not denser, so a trajectory point at `t_k` lines
up exactly with the reachable set at step `k` for the inside-the-polygon
sanity check `experiments/README.md` describes. Computed in plain Python
`float` (binary64): plenty for a plot overlay, and this file makes no
soundness claim the way the Lean side's own arithmetic does.

The trajectories: `X0`'s own centre, every one of its `2^h` sign-combination
corners (`h` the number of generator columns; `4` for this harness's
2-generator configs), and a handful of fixed-seed pseudo-random interior
points (`random.Random(1234)`, reproducible run to run) -- about ten in all.
Every one is a straight run of `x y` rows (open, not closed -- a trajectory
is a path, not a polygon), separated by a `nan nan` row, so the whole file is
one pgfplots `\\addplot table` with `unbounded coords=jump`.

Usage:
    python3 simulate.py <config.json> <out.dat> [--interior N]
"""

# Authors:       Tobias Ladner
# Written:       27-September-2026

from __future__ import annotations

import argparse
import itertools
import json
import math
import random
import sys
from pathlib import Path


def parse_rational(s: str) -> float:
    """`"m"` or `"m/d"` as a `float` -- the same literal shape the config's
    rational strings use, `Bench.Rational.parseExact`'s Python twin, with no
    exactness check (a plot overlay only)."""
    parts = s.split("/")
    if len(parts) == 1:
        return float(parts[0])
    if len(parts) == 2:
        return float(parts[0]) / float(parts[1])
    raise ValueError(f"not a rational literal: {s}")


def load_config(path: Path) -> dict:
    raw = json.loads(path.read_text())
    a = parse_rational(raw["system"]["a"])
    b = parse_rational(raw["system"]["b"])
    dt = parse_rational(raw["dt"])
    center = [parse_rational(v) for v in raw["x0"]["center"]]
    gens = [[parse_rational(v) for v in row] for row in raw["x0"]["generators"]]
    return {"a": a, "b": b, "dt": dt, "steps": raw["steps"], "center": center, "gens": gens}


def start_points(center: list[float], gens: list[list[float]],
                  n_interior: int) -> list[tuple[float, float]]:
    """The centre, every `2^h` sign-combination corner of `X0`, and
    `n_interior` fixed-seed pseudo-random interior points (each coordinate a
    random combination of the generators with coefficients in `(-1, 1)`)."""
    h = len(gens[0]) if gens and gens[0] else 0
    pts = [(center[0], center[1])]
    for signs in itertools.product((-1.0, 1.0), repeat=h):
        x = center[0] + sum(s * gens[0][j] for j, s in enumerate(signs))
        y = center[1] + sum(s * gens[1][j] for j, s in enumerate(signs))
        pts.append((x, y))
    rng = random.Random(1234)
    for _ in range(n_interior):
        coeffs = [rng.uniform(-1.0, 1.0) for _ in range(h)]
        x = center[0] + sum(c * gens[0][j] for j, c in enumerate(coeffs))
        y = center[1] + sum(c * gens[1][j] for j, c in enumerate(coeffs))
        pts.append((x, y))
    return pts


def trajectory(a: float, b: float, dt: float, steps: int,
               p0: tuple[float, float]) -> list[tuple[float, float]]:
    """`e^{A t_k} p0` at every sample time `t_k = k * dt`, `k = 0, ..., steps`,
    `e^{At} = e^{at} [[cos(bt), sin(bt)], [-sin(bt), cos(bt)]]` applied
    directly -- exact in the reals, evaluated in `float`."""
    pts = []
    for k in range(steps + 1):
        t = k * dt
        scale = math.exp(a * t)
        cos_bt = math.cos(b * t)
        sin_bt = math.sin(b * t)
        x = scale * (cos_bt * p0[0] + sin_bt * p0[1])
        y = scale * (-sin_bt * p0[0] + cos_bt * p0[1])
        pts.append((x, y))
    return pts


def write_merged(path: Path, trajectories: list[list[tuple[float, float]]]) -> None:
    with path.open("w") as f:
        f.write("# x y\n")
        for i, traj in enumerate(trajectories):
            if i > 0:
                f.write("nan nan\n")
            for x, y in traj:
                f.write(f"{x:.6g} {y:.6g}\n")


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                  formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("config", type=Path)
    ap.add_argument("out", type=Path)
    ap.add_argument("--interior", type=int, default=5,
                     help="number of fixed-seed pseudo-random interior points (default: 5)")
    args = ap.parse_args(argv)

    cfg = load_config(args.config)
    pts = start_points(cfg["center"], cfg["gens"], args.interior)
    trajectories = [trajectory(cfg["a"], cfg["b"], cfg["dt"], cfg["steps"], p0) for p0 in pts]

    args.out.parent.mkdir(parents=True, exist_ok=True)
    write_merged(args.out, trajectories)
    print(f"simulate: wrote {args.out} ({len(trajectories)} trajectories, "
          f"{cfg['steps'] + 1} samples each)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
