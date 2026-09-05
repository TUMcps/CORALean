import CORALean.NN.Layers.Activation
import CORALean.NN.Layers.BatchNorm
import CORALean.NN.Layers.Convolution
import CORALean.NN.Layers.Curvature
import CORALean.NN.Layers.Linear
import CORALean.NN.Layers.Pooling
import CORALean.NN.Layers.PolyRelaxation
import CORALean.NN.Layers.PolySampling
import CORALean.NN.Layers.ReLU
import CORALean.NN.Layers.Reshape
import CORALean.NN.Layers.Sigmoid
import CORALean.NN.Layers.Softmax
import CORALean.NN.Layers.Tanh

/-!
# The standard layers, collected

Three kinds, and the division is the useful thing to know about this directory.

**Linear in disguise.** `Linear` itself, and then `Convolution`, average pooling
in `Pooling`, and `BatchNorm`: each of those three is `Layer.linear` at a
particular matrix, by definition and not up to a lemma. So each contributes a
matrix and a proof that the matrix computes what the layer is named after, and
no propagation and no soundness argument of its own. At a representation closed
under `mtimes` and `plus` all four are exact.

**Relaxations.** `ReLU`, `Sigmoid` and `Tanh` are `Activation` at a `Relaxation`
and nothing else: an affine map per neuron and the error to allow for, which is
where every bit of a network's precision is decided. `ReLU` gets its slope from
convexity, the other two from `Curvature`, which brackets `σ'` over the box.
`PolyRelaxation` is the same at degree `n`, `Relaxation` its order-1 case, and
`PolySampling` the only error bound here needing no closed form: sample the box,
and pad by what a Lipschitz bound allows between samples.

**Neither.** `Reshape` is a relabelling, and the only layer here that is *exact*
rather than outer — it asks for `Reindex`. Max pooling in `Pooling` and `Softmax`
need enclosures of their own: the first because its output depends on a window
rather than on a coordinate, the second on every coordinate at once.
-/
