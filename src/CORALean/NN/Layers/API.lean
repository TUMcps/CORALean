import CORALean.NN.Layers.Activation
import CORALean.NN.Layers.BatchNorm
import CORALean.NN.Layers.Convolution
import CORALean.NN.Layers.Linear
import CORALean.NN.Layers.Pooling
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

**Relaxations.** `ReLU`, `Sigmoid` and `Tanh` are `Activation` at a
`Relaxation` and nothing else: an affine map per neuron and the error to allow
for, which is where every bit of a network's precision is decided. `ReLU`
carries a slope, convexity being enough to justify one; the other two carry
none, monotonicity alone certifying no better than the output range.

**Neither.** `Reshape` is a relabelling, and the only layer here that is
*exact* rather than outer — it asks for `Reindex`, whose guarantee is an
equality. Max pooling in `Pooling` and `Softmax` need enclosures of their own:
the first because its output depends on a window rather than on a coordinate,
the second because its output depends on every coordinate at once. Each file
says exactly where `Relaxation` stops reaching.
-/
