import CORALean.NN.Layers.Cost.API
import CORALean.NN.Layers.Definitions.API
import CORALean.NN.Layers.Instances
import CORALean.NN.Layers.Layer
import CORALean.NN.Layers.Operations.API
import CORALean.NN.Layers.Theorems.API

/-!
# The standard layers, collected

`Operations/` holds the layers, each written once over the scalar and each run at `ℝ` and at a
machine scalar alike; `Theorems/` proves them sound at every scalar. `Definitions/` holds what
they mean — the functions over ℝ a layer encloses and never runs, the soundness predicates, and
the exact relaxations and polynomial fits that exist only over ℝ, being built from `Real.exp` or
by choice; `Theorems/Real/` holds what only ℝ can state of those. `Cost/` prices the linear layer.
-/
