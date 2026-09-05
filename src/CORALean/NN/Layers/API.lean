import CORALean.NN.Layers.Activation
import CORALean.NN.Layers.BatchNorm
import CORALean.NN.Layers.Convolution
import CORALean.NN.Layers.Curvature
import CORALean.NN.Layers.Linear
import CORALean.NN.Layers.Pooling
import CORALean.NN.Layers.PolyAffineConj
import CORALean.NN.Layers.PolyDerivBound
import CORALean.NN.Layers.PolyFit
import CORALean.NN.Layers.PolyRelaxation
import CORALean.NN.Layers.PolySampling
import CORALean.NN.Layers.ReLU
import CORALean.NN.Layers.Reshape
import CORALean.NN.Layers.Sigmoid
import CORALean.NN.Layers.SigmoidPoly
import CORALean.NN.Layers.Softmax
import CORALean.NN.Layers.Tanh
import CORALean.NN.Layers.TanhPoly

/-!
# The standard layers, collected

Three kinds, and the division is the useful thing to know about this directory.

**Linear in disguise.** `Linear`, and then `Convolution`, average pooling in
`Pooling` and `BatchNorm`: each is `Layer.linear` at a particular matrix, by
definition and not up to a lemma, so each contributes a matrix and a proof of
what that matrix computes and nothing else. At a representation closed under
`mtimes` and `plus` all four are exact.

**Relaxations.** `ReLU`, `Sigmoid` and `Tanh` are `Activation` at a `Relaxation`
and nothing else: an affine map per neuron and the error to allow for, which is
where every bit of a network's precision is decided. `ReLU` gets its slope from
convexity, the other two from `Curvature`, which brackets `σ'` over the box.
`PolyRelaxation` is the same at degree `n`, `Relaxation` its order-1 case, and
`PolySampling` bounds its error by sampling. `PolyDerivBound` is what that bound
needs and `PolyFit` what it does not: a fit owes no proof. `SigmoidPoly` and
`TanhPoly` instantiate them, the second through `PolyAffineConj`.

**Neither.** `Reshape` is a relabelling, and the only layer here that is *exact*
rather than outer — it asks for `Reindex`. Max pooling in `Pooling` and `Softmax`
need enclosures of their own: the first because its output depends on a window
rather than on a coordinate, the second on every coordinate at once.
-/
