import CORALean.NN.Float.Layers.API

/-!
# Neural network verification over a floating-point scalar, collected

Layers only, and that is the finding rather than an omission. `Layer` is a
structure over any `ContSet` whose ambient type is `Vec ℝ n`, and a float
representation is one through `InflatedContSet` — so `NeuralNetwork`,
`propagate`, `propagate_outer`, `holds_of_propagate` and the robustness bounds
all run at a float representation with nothing rewritten. Only the layer
constructors name the scalar their weights are stored in, and only they are
duplicated here.

What a float layer encloses is the exact function the stored floats denote:
`W x + b` at the weights that were read in, `σ` itself at an activation. So the
guarantee is the same image inclusion the exact layer proves, and composing it
along the network is the same induction.

The rounding enters in four places and no others: the representation's own
operations, which charge it to their error box; a relaxation's error, widened
outward by `Relaxation.box`; the relaxation's own arithmetic, where `ReLU`
rounds its gap up and `Sigmoid` rounds an exponential and a reciprocal; and the
two layers that are neither linear nor relaxations, where max pooling rounds its
window gap up and softmax rounds a denominator down. Slope and offset are never
constrained — `Relaxation.sound` states an inequality against `error`, so
anything stored in them is sound as it stands, and that is why this layer costs
so much less than it looks.

The layers that round *nowhere* are the ones whose weights are placed rather
than computed: `Linear`, `Convolution`, and the selection matrix max pooling
propagates through. A stencil matrix's entry is one kernel weight or zero, so
`toRealMat_tapMat` is an equality with no hypothesis and the stored kernel
denotes the convolution exactly.
-/
