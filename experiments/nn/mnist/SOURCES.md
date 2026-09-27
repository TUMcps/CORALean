# Sources for the `nn-mnist` experiment

## Networks: VNN-COMP 2021 `mnistfc`

`stanleybak/vnncomp2021` has been renamed/transferred to `VNN-COMP/vnncomp2021`
on GitHub; both URLs resolve, the `raw.githubusercontent.com` link below through
a redirect. Not gzipped, downloaded directly as `.onnx`.

| file | URL | sha256 (ONNX) |
| --- | --- | --- |
| small (`mnist-net_256x2.onnx`, 2 hidden layers) | `https://raw.githubusercontent.com/VNN-COMP/vnncomp2021/main/benchmarks/mnistfc/mnist-net_256x2.onnx` | `3a5c9730d60bbf1f9b030e731b438436581efd7c00a28ab683c1ec4b6d3449c4` |
| medium (`mnist-net_256x4.onnx`, 4 hidden layers) | `https://raw.githubusercontent.com/VNN-COMP/vnncomp2021/main/benchmarks/mnistfc/mnist-net_256x4.onnx` | `fb53b4745b5882be61325ec24908f9fb036010cd79c99c20bb0b75e3b359acae` |
| large (`mnist-net_256x6.onnx`, 6 hidden layers) | `https://raw.githubusercontent.com/VNN-COMP/vnncomp2021/main/benchmarks/mnistfc/mnist-net_256x6.onnx` | `295c175d7b477b2f05dd4787bcabacf8c10d02d7d4b31f8682ea0d8844c6b0a6` |

Each is `Flatten(axis=1) -> (Gemm -> Relu)* -> Gemm` (opset 9), no input
normalisation node (no `Sub`/`Div`): input `0` is `[1, 784, 1]`, flattened to
784, output `12`/`20`/`28` is `[1, 10]`. Every `Gemm` has `alpha = beta = 1`,
`transB = 1`, i.e. `x @ W^T + b` for a PyTorch-`nn.Linear`-style `weight`
initializer of shape `[out, in]` -- read directly, no transpose needed.
Confirmed by inspecting `onnx.load(...).graph` in the throwaway venv (see
below); `python3 -c "import onnx; ..."` on each file reproduces the node list.

Small's graph, as inspected (medium/large repeat the `Gemm -> Relu` pair):

```
Flatten  in=['0']                                  out=['7']
Gemm     in=['7','layers.0.weight','layers.0.bias'] out=['8']   # 784 -> 256
Relu     in=['8']                                   out=['9']
Gemm     in=['9','layers.2.weight','layers.2.bias'] out=['10']  # 256 -> 256
Relu     in=['10']                                  out=['11']
Gemm     in=['11','layers.4.weight','layers.4.bias'] out=['12'] # 256 -> 10
```

### Conversion

```
python3 -m venv /tmp/.../venv && /tmp/.../venv/bin/pip install onnx numpy
/tmp/.../venv/bin/python3 experiments/nn/mnist/convert_onnx.py \
  <downloaded>/mnist-net_256x2.onnx experiments/nn/mnist/nets/small.txt
/tmp/.../venv/bin/python3 experiments/nn/mnist/convert_onnx.py \
  <downloaded>/mnist-net_256x4.onnx experiments/nn/mnist/nets/medium.txt
/tmp/.../venv/bin/python3 experiments/nn/mnist/convert_onnx.py \
  <downloaded>/mnist-net_256x6.onnx experiments/nn/mnist/nets/large.txt
```

`convert_onnx.py`'s module docstring gives the exact output format. sha256 of
the converted files:

| file | sha256 |
| --- | --- |
| `nets/small.txt` | `d7b42778c5d91a775169c3371bfefd0d29aec3b86fa4e1e995fd15b22e2681d0` |
| `nets/medium.txt` | `7a7714a3a497ae2b5661a0d3ed901309e2b9c8b4eeb091c13c4285e2e557c4be` |
| `nets/large.txt` | `3763debbb95f6e49eae10a46e7d8a7fe23d9146dd77d37684905f593ba4984f5` |

## Data: MNIST test set, first 100 images

MNIST is CC BY-SA 3.0 (Yann LeCun, Corinna Cortes, Christopher J.C. Burges;
http://yann.lecun.com/exdb/mnist/). Fetched from the `cvdf-datasets` mirror
(the same content Google's TensorFlow datasets pipeline uses), rather than
`yann.lecun.com` directly, which has been unreliable for scripted fetches:

| file | URL | sha256 (gzip) |
| --- | --- | --- |
| `t10k-images-idx3-ubyte.gz` | `https://storage.googleapis.com/cvdf-datasets/mnist/t10k-images-idx3-ubyte.gz` | `8d422c7b0a1c1c79245a5bcf07fe86e33eeafee792b84584aec276f5a2dbc4e6` |
| `t10k-labels-idx1-ubyte.gz` | `https://storage.googleapis.com/cvdf-datasets/mnist/t10k-labels-idx1-ubyte.gz` | `f7ae60f92e00ec6debd23a6088c31dbd2371eca3ffa0defaefb259924204aec6` |

### Conversion

```
python3 experiments/nn/mnist/fetch_mnist.py <scratch dir> \
  experiments/nn/mnist/data/mnist_test_first100.txt
```

Standard library only (`urllib`, `gzip`, `hashlib`, `struct`) -- rerunning it
regenerates the committed file. It prints each downloaded file's sha256 and the
converted file's own. The first 100 images/labels of the IDX test set, one
line per image: `label` then 784 decimal `uint8` pixel values, row-major,
space-separated. sha256 of the converted file:

`fe12f9d4baa4820b7d6fac87c49fa2f1f0cd36f2b815d1ea39423834c31f9b44`

Image `0`'s label is `7`, matching the well-known first MNIST test image.

## Input scaling

The benchmark's own convention (VNN-COMP `mnistfc`, and CORA's own reachability
papers reading this benchmark) is `x = pixel / 255 ∈ [0, 1]`, with no further
per-pixel normalisation -- consistent with the ONNX graph carrying no `Sub`/`Div`
node. `nn-mnist` encloses each `k / 255` as described in
`experiments/README.md`'s "MNIST rounding-error ablation" section.
