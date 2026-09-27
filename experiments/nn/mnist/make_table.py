#!/usr/bin/env python3
"""Turns `nn-mnist`'s run JSONs into the ablation table: `mnist_table.tex`
(a booktabs table body) and `mnist_table.csv` (the same numbers).

Standard library only. Reads `<results>/nn-mnist/<net>/<label>.json` for
every net in `small medium large` and every label `run_mnist.sh` writes
(`dyadic-binary4` .. `dyadic-binary64`, `float`, and, where present,
`nearest-binary4` .. `nearest-binary64`) -- a label that is not there is
skipped rather than failing the table, so a partial sweep still prints
whatever it has.

Column headers use the paper's own precision labels (`p = 4/8/16/32/64`, the
IEEE format's total width, not its significand) rather than `binaryN`; a
`nearest-*` column is headed "round-to-nearest (as in CORA), unverified" and
its certified cell is always "n/a (unsound)" -- `Mnist.lean`'s own JSON
already carries `certified_fraction` as that string wherever `meta.sound` is
`false`, so this script only ever prints it, never recomputes it.

Usage:
    python3 make_table.py <results-dir> <out-prefix>

writes `<out-prefix>.tex` and `<out-prefix>.csv`.
"""

# Authors:       Tobias Ladner
# Written:       27-September-2026
# Last update:   ---
# Last revision: ---


# ----------------------------------------  BEGIN CODE  ---------------------------------------- #

import csv
import json
import os
import sys

NETS = ["small", "medium", "large"]
DYADIC_FORMATS = ["binary4", "binary8", "binary16", "binary32", "binary64"]
# the paper's own precision label: the IEEE format's total bit width, not its significand
PAPER_LABEL = {"binary4": "p=4", "binary8": "p=8", "binary16": "p=16",
               "binary32": "p=32", "binary64": "p=64"}

# (label, column header) -- `nearest-*` columns are added only if their JSON exists
COLUMNS = (
    [(f"dyadic-{f}", PAPER_LABEL[f]) for f in DYADIC_FORMATS]
    + [("float", "float (p=64)")]
    + [(f"nearest-{f}", f"round-to-nearest (as in CORA), unverified, {PAPER_LABEL[f]}")
       for f in DYADIC_FORMATS]
)


def load(results_dir: str, net: str, label: str):
    path = os.path.join(results_dir, "nn-mnist", net, f"{label}.json")
    if not os.path.exists(path):
        return None
    with open(path) as f:
        return json.load(f)


def certified_text(s) -> str:
    """The summary's own `certified_fraction`: a string ("n/a (unsound)")
    wherever `Mnist.lean` marked the run unsound, else a percentage."""
    c = s["certified_fraction"]
    return c if isinstance(c, str) else f"{100.0 * c:.0f}%"


def cell_text(doc) -> str:
    """`mean error radius / % certified / median ms`, `doc`'s own summary."""
    s = doc["summary"]
    mean_r = s["error_radius"]["mean"]
    median_ms = s["median_time_ns"] / 1e6
    return f"{mean_r:.3g} / {certified_text(s)} / {median_ms:.2f}"


# =====================================  MAIN DEFINITION  ====================================== #

def build_table(results_dir: str):
    """`(present_columns, rows)`: `present_columns` the subset of `COLUMNS`
    with at least one net's JSON, `rows` one `(net, {label: doc_or_None})` per net."""
    docs = {net: {label: load(results_dir, net, label) for label, _ in COLUMNS} for net in NETS}
    present = [(label, header) for label, header in COLUMNS
               if any(docs[net][label] is not None for net in NETS)]
    return present, docs


def write_tex(path: str, present, docs) -> None:
    lines = []
    for net in NETS:
        cells = []
        for label, _ in present:
            doc = docs[net][label]
            cells.append(cell_text(doc) if doc is not None else "--")
        lines.append(f"{net} & " + " & ".join(cells) + r" \\")
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")


def write_csv(path: str, present, docs) -> None:
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["net", "precision", "mean_error_radius", "max_error_radius",
                    "certified", "accuracy_pct", "median_time_ms"])
        for net in NETS:
            for label, header in present:
                doc = docs[net][label]
                if doc is None:
                    continue
                s = doc["summary"]
                w.writerow([
                    net, header,
                    s["error_radius"]["mean"], s["error_radius"]["max"],
                    certified_text(s), 100.0 * s["accuracy"],
                    s["median_time_ns"] / 1e6,
                ])


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("usage: make_table.py <results-dir> <out-prefix>", file=sys.stderr)
        sys.exit(1)
    results_dir, out_prefix = sys.argv[1], sys.argv[2]
    present, docs = build_table(results_dir)
    if not present:
        print(f"make_table: no nn-mnist JSON found under {results_dir}", file=sys.stderr)
        sys.exit(1)
    write_tex(f"{out_prefix}.tex", present, docs)
    write_csv(f"{out_prefix}.csv", present, docs)
    print(f"make_table: wrote {out_prefix}.tex and {out_prefix}.csv "
          f"({len(present)} precision column(s))")


# ---------------------------------------  END OF CODE  ---------------------------------------- #
