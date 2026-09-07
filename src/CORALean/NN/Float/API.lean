import CORALean.NN.Float.Layers.API

/-!
# Neural network verification over a floating-point scalar, collected

Layers only, and that is the finding rather than an omission. `Layer` is a
structure over any `ContSet` whose ambient type is `Vec ℝ n`, and a float
representation is one through `InflatedContSet` — so `NeuralNetwork`, `enclose`
and everything in `NN/Theorems` run at a float representation with nothing
rewritten. Only the layer constructors name the scalar their weights are stored
in.

What a float layer encloses is the exact function the stored floats denote:
`W x + b` at the weights read in, `σ` itself at an activation. So the guarantee
is the same image inclusion the exact layer proves.

The rounding enters in four places and no others: the representation's own
operations, which charge it to their error box; a relaxation's error, widened
outward by `Relaxation.box`; the relaxation's own arithmetic, where `ReLU` rounds
its gap up and `Sigmoid` an exponential and a reciprocal; and max pooling's window
gap and softmax's denominator. Slope and offset are never constrained,
`Relaxation.sound` stating an inequality against `error`.

The layers that round *nowhere* are the ones whose weights are placed rather than
computed: `Linear`, `Convolution`, and the selection matrix max pooling
encloses through, `toRealMat_tapMat` being an equality with no hypothesis.
-/
