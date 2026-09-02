import CORALean.NN.Float.Layers.Activation
import CORALean.NN.Float.Layers.Linear
import CORALean.NN.Float.Layers.ReLU

/-!
# The standard layers over a floating-point scalar, collected

Three files where the exact layer has five, and the two that are missing are
missing for one reason.

`Linear` rounds nowhere: `mtimes` and `plus` pay their own rounding into the
representation's error box, so the layer is the exact one term for term.
`Activation` rounds in one place, widening `offset ± error` outward, and `ReLU`
in one more, rounding its gap up — and its slope, the one thing the exact layer
computes with a division, needs no division here at all, since any value in
`[0, 1]` is sound and `clampUnit` puts an arbitrary candidate there exactly.

`Sigmoid` and `Tanh` have no float counterpart, and not because the relaxation
is hard: it is `Relaxation.ofMonotone`, already here, and it asks only for the
value of `σ` at the two ends of each neuron's range. `FloatOps` cannot supply
one. It has `+`, `*`, `min`, `max`, negation and a halving; it has no `exp`, no
division, and no series evaluation, so there is no `Enclosure 𝕋 sigmoid` and no
`Enclosure 𝕋 Real.tanh` to hand it. The only enclosure available without one is
the constant range — `[0, 1]` for sigmoid, `[-1, 1]` for tanh — which is sound
and throws away everything the layer was computing bounds for.

Closing that needs a directed-rounding `exp` in `FloatOps`, with instances for
`Dyadic` and for ℝ, and a truncated-series argument bounding the tail: a piece
of `Global/Float` rather than of this directory. `Enclosure` is the interface it
would arrive at, and nothing else here would change.
-/
