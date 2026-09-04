import CORALean.NN.Float.Layers.Activation
import CORALean.NN.Float.Layers.Convolution
import CORALean.NN.Float.Layers.Linear
import CORALean.NN.Float.Layers.Pooling
import CORALean.NN.Float.Layers.ReLU
import CORALean.NN.Float.Layers.Sigmoid
import CORALean.NN.Float.Layers.Softmax
import CORALean.NN.Float.Layers.Tanh

/-!
# The standard layers over a floating-point scalar, collected

Each rounds in as few places as it can, and two of the exact layer's ten are
missing on purpose.

`Linear` rounds nowhere: `mtimes` and `plus` pay their own rounding into the
representation's error box. `Convolution` and max pooling inherit that, a stencil
matrix's entries being *placed* rather than summed.

`Activation` rounds in one place, widening `offset ± error` outward, and `ReLU`
in one more, rounding its gap up — its slope needs no division here, any value in
`[0, 1]` being sound. Max pooling is the same shape a window wider.

`Sigmoid` and `Tanh` needed something new, and it is in `Global/Float`:
`expDown`, a directed exponential out of `half`, `+` and `*`, and a
`divUp`/`divDown` pair. `Softmax` is where that exponential's asymmetry is paid
for: its lower bound would need `expUp`, which is not total, so it takes one from
the normalization instead.

`Reshape` and `BatchNorm` have no file here, and neither is an omission.
`Layer.reshape` carries no weights, so the exact constructor is already the float
one; `Layer.batchNorm` is `Layer.linear` at a folded scale and shift, so
`Float.Layer.linear` is its counterpart.
-/
