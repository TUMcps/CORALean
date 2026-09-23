import CORALean.NN.Float.BucketTolerance
import CORALean.NN.Float.CompressionPreprocessing
import CORALean.NN.Float.Layers.API
import CORALean.NN.Float.ReduceOnTheFly
import CORALean.NN.Float.ReducibleNetwork
import CORALean.NN.Float.Theorems.API

/-!
# Neural network verification over a floating-point scalar, collected

`Layer` is a structure over any `ContSet` whose ambient type is `Vec ℝ n`, and a float
representation is one through `InflatedContSet` — so `NeuralNetwork`, `enclose` and all of
`NN/Theorems` run at a float representation unchanged. Only what reads weights is here: the
layer constructors, and network reduction over a `ReducibleNetwork` — `BucketTolerance`,
`ReduceOnTheFly`, `CompressionPreprocessing`, proved sound in `Theorems/`.

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
