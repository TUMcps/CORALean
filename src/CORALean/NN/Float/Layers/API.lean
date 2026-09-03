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
representation's error box, so the layer is the exact one term for term.
`Convolution` and max pooling in `Pooling` inherit that — a stencil matrix's
entries are *placed* rather than summed, so `toRealMat_tapMat` is an equality
with no hypothesis and the stored kernel denotes the convolution exactly.

`Activation` rounds in one place, widening `offset ± error` outward, and `ReLU`
in one more, rounding its gap up — and its slope, the one thing the exact layer
computes with a division, needs no division here at all, since any value in
`[0, 1]` is sound and `clampUnit` puts an arbitrary candidate there exactly. Max
pooling is the same shape a window wider: the pivot is free and only the gap
rounds.

`Sigmoid` and `Tanh` are the two that needed something new, and it is in
`Global/Float` rather than here: `expDown`, a directed exponential built by
argument reduction and repeated squaring out of `half`, `+` and `*`, and a
`divUp`/`divDown` pair, a logistic function being a quotient. Given those the
relaxation is `Relaxation.ofMonotone` unchanged, since an `Enclosure` is all it
ever asked for.

`Softmax` is where the asymmetry of that exponential is finally paid for. Its
lower bound would need `expUp`, which is not total, so the layer computes none
and takes its lower bound from the normalization instead: the outputs sum to
one, so what the others' *upper* bounds leave over is a lower bound on this one.
The constraint the standard treatment discards is not a refinement here, it is
the only lower bound there is.

`Reshape` and `BatchNorm` have no file here, and neither is an omission.
`Layer.reshape` carries no weights, so there is no scalar to name — the exact
constructor is already the float one, and what the float layer owes is the
`Reindex` instances, which `ContSet/*/Float` has. `Layer.batchNorm` is
`Layer.linear` at a folded scale and shift, so `Float.Layer.linear` is its float
counterpart; the fold itself is parameter arithmetic done once when a network is
read, and `FloatOps` having no square root is no obstacle to it, since what is
verified is the affine map the folded numbers describe.

Both `Sigmoid`/`Tanh` and `Softmax` carry a reduction depth `k`, and it is
precision alone — every `k` is sound, a larger one tighter — because the
enclosure is stated against the exact function rather than against a nominal
float value.
-/
