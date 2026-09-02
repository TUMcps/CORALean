import CORALean.NN.Layers.Activation
import CORALean.NN.Layers.Linear
import CORALean.NN.Layers.ReLU
import CORALean.NN.Layers.Sigmoid
import CORALean.NN.Layers.Tanh

/-!
# The standard layers, collected

`Linear` is the only one a representation closed under `mtimes` and `plus`
computes exactly. The rest are activations, and `Activation` is the shape all of
them take: an affine map per neuron and the error to allow for, which is where
every bit of a network's precision is decided.

`ReLU` carries a slope, convexity being enough to justify one; `Sigmoid` and
`Tanh` currently carry none, monotonicity alone certifying no better than the
output range. Each file says what it would take to improve on that.
-/
