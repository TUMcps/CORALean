import CORALean.NN.Float.Layers.Activation
import CORALean.NN.Float.Layers.Linear
import CORALean.NN.Float.Layers.ReLU
import CORALean.NN.Float.Layers.Sigmoid
import CORALean.NN.Float.Layers.Tanh

/-!
# The standard layers over a floating-point scalar, collected

The same five the exact layer has, each rounding in as few places as it can.

`Linear` rounds nowhere: `mtimes` and `plus` pay their own rounding into the
representation's error box, so the layer is the exact one term for term.
`Activation` rounds in one place, widening `offset ± error` outward, and `ReLU`
in one more, rounding its gap up — and its slope, the one thing the exact layer
computes with a division, needs no division here at all, since any value in
`[0, 1]` is sound and `clampUnit` puts an arbitrary candidate there exactly.

`Sigmoid` and `Tanh` are the two that needed something new, and it is in
`Global/Float` rather than here: `expDown`, a directed exponential built by
argument reduction and repeated squaring out of `half`, `+` and `*`, and a
`divUp`/`divDown` pair, a logistic function being a quotient. Given those the
relaxation is `Relaxation.ofMonotone` unchanged, since an `Enclosure` is all it
ever asked for. `Tanh` writes no exponential of its own: `tanh t = 2 σ(2t) - 1`,
and the doubled argument rounds outward in the direction being bounded.

Both carry a reduction depth `k`, and it is precision alone — every `k` is
sound, a larger one tighter — because the enclosure is stated against the exact
`σ` rather than against a nominal float value.
-/
