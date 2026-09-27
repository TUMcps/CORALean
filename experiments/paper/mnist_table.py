#!/usr/bin/env python3
"""mnist_table.py -- the paper's own nn-mnist table and net-architecture
table, from `<results>/nn-mnist/<net>/<label>.json`
(`experiments/nn/mnist/run_mnist.sh`'s own output; `make_table.py`, already
in that directory, reads the same files into a wider ablation table over
every precision -- this is the paper's own narrower layout, adapting it
rather than changing that script).

Standard library only. For `net` in `small`, `medium`, `large`:

* `mnist_table.{tex,csv}`: one row per net, two cells (mean output radius,
  percent certified) per column, one column per `p = 16, 32, 64` (Dyadic,
  outward rounding) and `p = 64 (Float)` (native binary64, outward
  rounding) -- `p = 4, 8` are excluded from the columns (both diverge for
  every net: accuracy and certification collapse) and noted in a line of
  their own instead of a column, per the paper's own review.
* `mnist_nets.csv`: net, hidden layers x neurons (parsed from
  `experiments/nn/mnist/nets/<net>.txt`'s own token format --
  `TokStream`'s own tokenizing in `MnistParse.lean`'s module docstring:
  `numLayers`, `inputDim`, then `outDim inDim hasBias` before each layer's
  own weights and, if `hasBias`, biases), parameter count (weights plus
  biases), and clean accuracy on the 100 images at Float.

Usage:
    python3 mnist_table.py <results-dir>
"""

# Authors:       Tobias Ladner
# Written:       27-September-2026

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import booktabs_rows, find_run, fmt_tex, load_json, write_csv, write_tex  # noqa: E402,E501

NETS = ["small", "medium", "large"]
COLUMNS = [("dyadic-binary16", "p=16"), ("dyadic-binary32", "p=32"),
           ("dyadic-binary64", "p=64"), ("float", "p=64 (Float)")]
DIVERGE_NOTE = "$p\\in\\{4,8\\}$: diverges for every network"


def load(results_dir: Path, net: str, label: str) -> dict | None:
    """`<results>/nn-mnist/<net>/<label>.json[.gz]` -- `nn-mnist`'s own JSON
    gets gzipped past `common.py`'s size threshold exactly like every other
    per-run JSON here, so this reads either spelling the same way."""
    run_path = find_run(results_dir / "nn-mnist" / net, label)
    return load_json(run_path) if run_path is not None else None


def mean_radius(doc: dict) -> float:
    """`summary.error_radius.mean` as a `float` -- `Mnist.lean`'s own JSON
    writer prints every number as a string, finite or not, unlike
    `FloatPrint`'s (a `Json.num` where it can be), so this always goes
    through `float(...)` rather than assuming either shape."""
    return float(doc["summary"]["error_radius"]["mean"])


def certified_cell(doc: dict) -> str:
    """`summary.certified_fraction`: a string ("n/a (unsound)") wherever
    `Mnist.lean` marked the run unsound, else a percentage, for a `.tex` cell."""
    c = doc["summary"]["certified_fraction"]
    if isinstance(c, str):
        return c
    return f"{100.0 * c:.0f}\\%"


def build_table(results_dir: Path) -> tuple[list[list], list[list]]:
    tex_rows, csv_rows = [], []
    for net in NETS:
        tex_cells = []
        csv_cells = []
        for label, _ in COLUMNS:
            doc = load(results_dir, net, label)
            if doc is None:
                tex_cells += ["--", "--"]
                csv_cells += ["", ""]
            else:
                r = mean_radius(doc)
                tex_cells += [fmt_tex(r), certified_cell(doc)]
                csv_cells += [repr(r), certified_cell(doc)]
        tex_rows.append([net] + tex_cells)
        csv_rows.append([net] + csv_cells)
    return tex_rows, csv_rows


def write_mnist_table(results_dir: Path) -> None:
    tex_rows, csv_rows = build_table(results_dir)
    header = ["net"]
    for _, label in COLUMNS:
        header += [f"{label}_mean_radius", f"{label}_certified"]
    write_csv(results_dir / "paper" / "mnist_table.csv", header, csv_rows)
    body = booktabs_rows(tex_rows) + "\\midrule\n" + \
        f"\\multicolumn{{{1 + 2 * len(COLUMNS)}}}{{l}}{{{DIVERGE_NOTE}}} \\\\\n"
    write_tex(results_dir / "paper" / "mnist_table.tex", body)


# ---------------------------------------------------------------------------
# mnist_nets.csv: architecture and parameter count, parsed from the net file
# itself, plus clean accuracy from the Float run's own summary.
# ---------------------------------------------------------------------------

def parse_net_architecture(net_path: Path) -> tuple[list[int], int]:
    """`(hidden_layer_sizes, num_parameters)` -- `hidden_layer_sizes` every
    layer's own output width but the last (the network's own class count),
    `num_parameters` every weight plus every bias the file holds."""
    toks = net_path.read_text().split()
    i = 0
    num_layers = int(toks[i]); i += 1
    i += 1  # input_dim, not needed beyond the first layer's own in_dim
    layer_out_dims = []
    params = 0
    for _ in range(num_layers):
        out_dim, in_dim, has_bias = int(toks[i]), int(toks[i + 1]), int(toks[i + 2])
        i += 3 + out_dim * in_dim + (out_dim if has_bias else 0)
        layer_out_dims.append(out_dim)
        params += out_dim * in_dim + (out_dim if has_bias else 0)
    return layer_out_dims[:-1], params


def hidden_layers_label(hidden_dims: list[int]) -> str:
    """`"2x256"` for two hidden layers of 256 each, or the plain list
    (`"256,128"`) if the widths are not all equal."""
    if not hidden_dims:
        return "0"
    if len(set(hidden_dims)) == 1:
        return f"{len(hidden_dims)}x{hidden_dims[0]}"
    return ",".join(str(d) for d in hidden_dims)


def write_mnist_nets(results_dir: Path, nets_dir: Path) -> None:
    rows = []
    for net in NETS:
        net_path = nets_dir / f"{net}.txt"
        if not net_path.exists():
            continue
        hidden_dims, params = parse_net_architecture(net_path)
        float_doc = load(results_dir, net, "float")
        accuracy = f"{100.0 * float_doc['summary']['accuracy']:.0f}%" \
            if float_doc is not None else ""
        rows.append([net, hidden_layers_label(hidden_dims), params, accuracy])
    write_csv(results_dir / "paper" / "mnist_nets.csv",
              ["net", "hidden_layers_x_neurons", "num_parameters", "clean_accuracy"], rows)


def main(argv: list[str]) -> int:
    results_dir = Path(argv[0]) if argv else Path("experiments/results-paper")
    nets_dir = Path("experiments/nn/mnist/nets")
    if not (results_dir / "nn-mnist").is_dir():
        print(f"mnist_table: no nn-mnist results under {results_dir}, skipping", file=sys.stderr)
        return 0
    (results_dir / "paper").mkdir(parents=True, exist_ok=True)
    write_mnist_table(results_dir)
    write_mnist_nets(results_dir, nets_dir)
    print(f"mnist_table: wrote mnist_table.{{tex,csv}} and mnist_nets.csv under "
          f"{results_dir / 'paper'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
