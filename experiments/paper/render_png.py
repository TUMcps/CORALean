#!/usr/bin/env python3
"""render_png.py -- optional PNG rendering of the paper's figures, for a quick
look without a LaTeX/pgfplots toolchain. NOT part of the artifact's own
reproduction contract (`make_paper.sh` calls this only if `matplotlib` is
importable, and skips it with a message otherwise): the pgfplots `.dat` files
`make_paper.sh` writes are the actual paper deliverable, this is a
convenience preview of the same numbers.

Untested on this harness (`matplotlib` is not installed here, and
installing it into a scratch venv failed -- no `python3-venv`); read
carefully before trusting its output on a machine where it does run.

For every config x scheme this results directory holds, one PNG overlaying
every number type's time-interval reach tube (`<type>-every10-ti-tube.dat`,
the thinned merged-polygon file `make_paper.sh` already produced) with `X0`
and `simulate.dat`'s trajectories; one more PNG for the precision ablation's
per-step error radius, log-scale, one line per `p`
(`paper/precision_eradius_p<P>.dat`).

Usage:
    python3 render_png.py <results-dir>
"""

# Authors:       Tobias Ladner
# Written:       27-September-2026

from __future__ import annotations

import sys
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Polygon  # noqa: E402

TYPE_COLORS = {
    "dyadic-binary64": ("tab:blue", "Dyadic $p=64$"),
    "float": ("tab:orange", "Float"),
    "nearest-binary64": ("tab:red", "round-to-nearest"),
    "cora": ("tab:green", "CORA"),
}


def read_polygons(path: Path) -> list[list[tuple[float, float]]]:
    """`path`'s `# x y` rows, `nan nan`-separated into one polygon (or
    trajectory) per block -- the shared format every `.dat` file this reads
    uses (`to_pgfplots.py`'s `write_merged`/`write_polygon`, `simulate.py`'s
    own `write_merged`). `[]` if `path` does not exist."""
    if not path.exists():
        return []
    blocks: list[list[tuple[float, float]]] = [[]]
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        x_s, y_s = line.split()
        if x_s.lower() == "nan":
            blocks.append([])
            continue
        blocks[-1].append((float(x_s), float(y_s)))
    return [b for b in blocks if b]


def render_reach_tube(results_dir: Path, config: str, scheme_dir: str, scheme_label: str,
                       out_dir: Path) -> None:
    fig, ax = plt.subplots(figsize=(6, 6))
    any_drawn = False
    for type_stem, (color, label) in TYPE_COLORS.items():
        # `-paper-ti-union.dat`'s rings are exterior-then-interiors (a hole's
        # own ring), which this draws as plain filled patches alike -- a
        # hole renders as a second, identically-coloured patch on top of the
        # outer one instead of a true cut-out. Fine for this optional,
        # untested preview; not for the paper's own even-odd-filled figure.
        tube_path = results_dir / config / scheme_dir / f"{type_stem}-paper-ti-union.dat"
        polys = read_polygons(tube_path)
        if not polys:
            continue
        any_drawn = True
        for i, poly in enumerate(polys):
            ax.add_patch(Polygon(poly, closed=True, facecolor=color, edgecolor=color,
                                  alpha=0.15, linewidth=0.5,
                                  label=label if i == 0 else None))
    x0_path = results_dir / config / scheme_dir / "dyadic-binary64-every10-x0.dat"
    for poly in read_polygons(x0_path):
        ax.add_patch(Polygon(poly, closed=True, facecolor="black", edgecolor="black",
                              alpha=0.4, label="$X_0$"))
        any_drawn = True
    sim_path = results_dir / config / "simulate-paper.dat"
    for traj in read_polygons(sim_path):
        xs, ys = zip(*traj)
        ax.plot(xs, ys, color="black", linewidth=0.3, alpha=0.6)
        any_drawn = True
    if not any_drawn:
        plt.close(fig)
        return
    ax.set_aspect("equal", adjustable="datalim")
    ax.set_xlabel("$x_1$")
    ax.set_ylabel("$x_2$")
    ax.set_title(f"{config}, scheme {scheme_label}")
    ax.legend(loc="upper right", fontsize="small")
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / f"{config}-{scheme_dir}.png"
    fig.savefig(out_path, dpi=150, bbox_inches="tight")
    plt.close(fig)
    print(f"render_png: wrote {out_path}")


def render_precision(results_dir: Path, out_dir: Path) -> None:
    fig, ax = plt.subplots(figsize=(6, 4))
    any_drawn = False
    for p in (4, 8, 16, 32, 64):
        path = results_dir / "paper" / f"precision_eradius_p{p}.dat"
        if not path.exists():
            continue
        ks, radii = [], []
        for line in path.read_text().splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            k_s, t_s, r_s = line.split()
            r = float(r_s)
            if r > 0:  # log scale: a zero radius (early steps) has no log
                ks.append(int(k_s))
                radii.append(r)
        if ks:
            ax.semilogy(ks, radii, label=f"$p={p}$")
            any_drawn = True
    if not any_drawn:
        plt.close(fig)
        return
    ax.set_xlabel("step $k$")
    ax.set_ylabel("error radius (log scale)")
    ax.set_title("Precision ablation: error-box growth")
    ax.legend(loc="best", fontsize="small")
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "precision.png"
    fig.savefig(out_path, dpi=150, bbox_inches="tight")
    plt.close(fig)
    print(f"render_png: wrote {out_path}")


def main(argv: list[str]) -> int:
    results_dir = Path(argv[0]) if argv else Path("experiments/results-paper")
    out_dir = results_dir / "paper" / "png"
    for config_dir in sorted(results_dir.iterdir()):
        if not config_dir.is_dir() or config_dir.name in ("nn", "paper"):
            continue
        for scheme_dir, scheme_label in (("headline-a", "a"), ("headline-b", "b")):
            if (config_dir / scheme_dir).is_dir():
                render_reach_tube(results_dir, config_dir.name, scheme_dir, scheme_label,
                                   out_dir)
    render_precision(results_dir, out_dir)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
