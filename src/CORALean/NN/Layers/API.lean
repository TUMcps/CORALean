import CORALean.NN.Layers.Activation
import CORALean.NN.Layers.ActivationPoly
import CORALean.NN.Layers.ActivationPolyInflate
import CORALean.NN.Layers.ActivationPolyRefine
import CORALean.NN.Layers.BatchNorm
import CORALean.NN.Layers.Convolution
import CORALean.NN.Layers.Curvature
import CORALean.NN.Layers.Linear
import CORALean.NN.Layers.Pooling
import CORALean.NN.Layers.PolyAffineConj
import CORALean.NN.Layers.PolyConvergence
import CORALean.NN.Layers.PolyDerivBound
import CORALean.NN.Layers.PolyFit
import CORALean.NN.Layers.PolyFitConvergence
import CORALean.NN.Layers.PolyRangeConvergence
import CORALean.NN.Layers.PolyRelaxation
import CORALean.NN.Layers.PolyRelaxationPad
import CORALean.NN.Layers.PolySampling
import CORALean.NN.Layers.ReLU
import CORALean.NN.Layers.Reshape
import CORALean.NN.Layers.Sigmoid
import CORALean.NN.Layers.SigmoidLinearSigmoid
import CORALean.NN.Layers.SigmoidPoly
import CORALean.NN.Layers.SigmoidPolyRefine
import CORALean.NN.Layers.Softmax
import CORALean.NN.Layers.Tanh
import CORALean.NN.Layers.TanhPoly

/-!
# The standard layers, collected

Three kinds, and the division is the useful thing to know about this directory.

**Linear in disguise.** `Linear`, and then `Convolution`, average pooling in `Pooling` and
`BatchNorm`: each is `Layer.linear` at a particular matrix, by definition and not up to a lemma,
so each contributes a matrix and a proof of what it computes. At a representation closed under
`mtimes` and `plus` all four are exact.

**Relaxations.** `ReLU`, `Sigmoid` and `Tanh` are `Activation` at a `Relaxation`: an affine map
per neuron and the error to allow for, where every bit of a network's precision is decided.
`ReLU` gets its slope from convexity, the other two from `Curvature`. `PolyRelaxation` is that at
degree `n` and `Relaxation` its order-1 case; `PolySampling` bounds the error, `PolyDerivBound`
is what that needs and `PolyFit` what it does not, `PolyConvergence` with `PolyFitConvergence`
drive it to zero, `PolyRelaxationPad` lifts one to a higher degree, and `SigmoidPoly` and
`TanhPoly` instantiate them (via `PolyAffineConj`). `ActivationPoly` propagates one per neuron at
`PolyZonotope` alone, `ActivationPolyInflate` says by how much it widens, `PolyRangeConvergence`
makes one order serve a whole range, `ActivationPolyRefine` is the three as a refinable layer,
`SigmoidPolyRefine` one at a real activation, and `SigmoidLinearSigmoid` a chain around a matrix.

**Neither.** `Reshape` is a relabelling, the only layer here *exact* rather than outer — it asks
for `Reindex`. Max pooling in `Pooling` and `Softmax` need their own enclosures: the first
because its output depends on a window not a coordinate, the second on every coordinate at once.
-/
