module

public import CORALean.NN.Operations.RefineLayer
public import CORALean.NN.Operations.RefinementRank
public import CORALean.NN.Operations.Sensitivity
public import CORALean.NN.Operations.WorstIndex

@[expose] public section

/-!
# Which layer to refine next

The paper's layer-wise heuristic [1, Def. 4.6]: `aux_layerRank` is [1, Eq. 28]'s
`‖σ_k‖₂`, the Euclidean norm of a layer's per-neuron `refinementRank`s, as CORA's
`norm(...)` takes it; `NeuralNetwork.aux_layerRank` reads that at the network's actual
sensitivity, `aux_worstLayer` names the largest of `k + 1` such ranks (`k̃ = argmax_k
‖σ_k‖₂`), and `refineWorst` spends a `refineLayer` step there.

Nothing here is proved and nothing here can be wrong: `encloseAt_outer` holds
at *every* schedule, so this file only decides where the next order is spent —
the same freedom `reduceBy_outer` has at every partition.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A layer's own rank, `‖σ_k‖₂` of its neurons' ranks [1, Eq. 28]: what the
layer-wise rule ranks layers by, the neurons of the layer it names all moving together. -/
noncomputable def aux_layerRank (J : Mat ℝ m n) (d : Vec ℝ n) : ℝ :=
  Real.sqrt (∑ j, refinementRank J d j ^ 2)

/-- The rank at what CORA actually backpropagates: the network's sensitivity at
a point of the input set, weighing the errors the layer's relaxation leaves. -/
noncomputable def Chain.aux_layerRank (c : Chain n m) (x d : Vec ℝ n) : ℝ :=
  _root_.CORALean.aux_layerRank (c.sensitivity x) d

/-- The layer the layer-wise rule refines next [1, Def. 4.6]: the largest
`aux_layerRank` of `k + 1` layers. -/
noncomputable def aux_worstLayer (r : Fin (k + 1) → ℝ) : Fin (k + 1) := worstIndex r


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layer-wise rule [1, Def. 4.6]: every neuron of the worst-ranked of
`k + 1` layers moves up an order. -/
noncomputable def Schedule.refineWorst (sch : Schedule) (r : Fin (k + 1) → ℝ) : Schedule :=
  Schedule.refineLayer sch (aux_worstLayer r)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
