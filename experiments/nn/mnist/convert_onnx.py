#!/usr/bin/env python3
"""Converts a VNN-COMP 2021 `mnistfc` ONNX network into the flat text format
`experiments/nn/mnist/nets/*.txt` -- see `SOURCES.md` for where the ONNX files
come from and the exact command this was run with.

Requires `onnx` and `numpy` -- the one script in this experiment that does, and
the one meant to run once per network rather than on every `run_mnist.sh`.

Every graph here is `Flatten -> (Gemm -> Relu)* -> Gemm`: no input
normalisation (no `Sub`/`Div` node) and `Gemm`'s `alpha = beta = 1`,
`transB = 1`, so each `Gemm` is exactly `x @ W^T + b` for a PyTorch-style
`weight` initializer of shape `[out, in]` -- read directly, no transpose
needed on this side. The output text format is whitespace-separated only, so a
reader may split it on any run of whitespace:

    <numLayers>
    <inputDim>
    <outDim_0> <inDim_0> <relu_0>
    <outDim_0 * inDim_0 hex8 float32 bit patterns, row-major>
    <outDim_0 hex8 float32 bit patterns>
    <outDim_1> <inDim_1> <relu_1>
    ...

`relu_i` is `1` for every hidden layer and `0` for the last (output) layer.
Every float is written as its raw IEEE 754 binary32 bit pattern, 8 lowercase
hex digits, which is exact and lets the Lean side decode sign/mantissa/exponent
without ever going through a decimal string.
"""

# Authors:       Tobias Ladner
# Written:       27-September-2026
# Last update:   ---
# Last revision: ---


# ----------------------------------------  BEGIN CODE  ---------------------------------------- #

import sys

import numpy as np
import onnx
from onnx import numpy_helper


def float32_hex(x: np.float32) -> str:
    """The bit pattern of `x`, 8 lowercase hex digits."""
    u = np.asarray(x, dtype=np.float32).view(np.uint32)
    return f"{int(u):08x}"


def load_gemm_layers(onnx_path: str):
    """Every `Gemm` node's `(weight, bias, relu_follows)`, in graph order, read
    off the initializers by name -- `Flatten` and `Relu` carry no weights and
    are inferred structurally (a `Relu` node follows every `Gemm` but the last)."""
    model = onnx.load(onnx_path)
    graph = model.graph
    init = {i.name: numpy_helper.to_array(i) for i in graph.initializer}
    gemm_nodes = [n for n in graph.node if n.op_type == "Gemm"]
    relu_nodes = {n.input[0] for n in graph.node if n.op_type == "Relu"}
    layers = []
    for n in gemm_nodes:
        alpha = next(a.f for a in n.attribute if a.name == "alpha")
        beta = next(a.f for a in n.attribute if a.name == "beta")
        transB = next(a.i for a in n.attribute if a.name == "transB")
        assert alpha == 1.0 and beta == 1.0 and transB == 1, (
            f"{onnx_path}: Gemm attributes {alpha=} {beta=} {transB=} are not the "
            "plain `x @ W^T + b` this converter assumes"
        )
        _, w_name, b_name = n.input
        W = init[w_name].astype(np.float32)  # [out, in]
        b = init[b_name].astype(np.float32)  # [out]
        relu_follows = n.output[0] in relu_nodes
        layers.append((W, b, relu_follows))
    return layers


# =====================================  MAIN DEFINITION  ====================================== #

def convert(onnx_path: str, out_path: str) -> None:
    layers = load_gemm_layers(onnx_path)
    assert not layers[-1][2], f"{onnx_path}: the last Gemm must not be followed by a Relu"
    assert all(relu for (_, _, relu) in layers[:-1]), (
        f"{onnx_path}: every Gemm but the last must be followed by a Relu"
    )
    input_dim = layers[0][0].shape[1]
    lines = [str(len(layers)), str(input_dim)]
    for W, b, relu in layers:
        out_dim, in_dim = W.shape
        lines.append(f"{out_dim} {in_dim} {1 if relu else 0}")
        lines.append(" ".join(float32_hex(w) for w in W.reshape(-1)))
        lines.append(" ".join(float32_hex(x) for x in b))
    with open(out_path, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"{onnx_path} -> {out_path}: {len(layers)} layers, input {input_dim}")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("usage: convert_onnx.py <in.onnx> <out.txt>", file=sys.stderr)
        sys.exit(1)
    convert(sys.argv[1], sys.argv[2])


# ---------------------------------------  END OF CODE  ---------------------------------------- #
