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

The rounding enters in three places and no others: the representation's own
operations, which charge it to their error box; a relaxation's error, widened
outward by `Relaxation.box`; and the relaxation's own arithmetic, where `ReLU`
rounds its gap up. Slope and offset are never constrained — `Relaxation.sound`
states an inequality against `error`, so anything stored in them is sound as it
stands, and that is why this layer costs so much less than it looks.
-/
