import CORALean.NN.Operations.RefineLayer
import CORALean.NN.Operations.RefinementRank
import CORALean.NN.Operations.Sensitivity
import CORALean.NN.Operations.WorstIndex

/-!
# Which layer to refine next

The paper's layer-wise heuristic [1, Def. 4.6]: `aux_layerRank` sums `refinementRank`
over a layer's neurons, `NeuralNetwork.aux_layerRank` reads that at the network's
actual sensitivity, `aux_worstLayer` names the largest of `k + 1` such ranks, and
`refineWorst` spends a `refineLayer` step there.

Nothing here is proved and nothing here can be wrong: `encloseAt_outer` holds
at *every* schedule, so this file only decides where the next order is spent —
the same freedom `reduceBy_outer` has at every partition. [1, Eq. 28] and
CORA's `norm(...)` take the 2-norm of the per-neuron ranks instead; the
aggregate only has to order layers, so which of the two is used is free.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A layer's own rank, its neurons' summed: what the layer-wise rule ranks
layers by, the neurons of the layer it names all moving together. -/
def aux_layerRank (J : Mat ℝ m n) (d : Vec ℝ n) : ℝ := ∑ j, refinementRank J d j

/-- The rank at what CORA actually backpropagates: the network's sensitivity at
a point of the input set, weighing the errors the layer's relaxation leaves. -/
noncomputable def Chain.aux_layerRank (c : Chain n m) (x d : Vec ℝ n) : ℝ :=
  _root_.CORALean.Real.aux_layerRank (c.sensitivity x) d

/-- The layer the layer-wise rule refines next [1, Def. 4.6]: the largest
`aux_layerRank` of `k + 1` layers. -/
noncomputable def aux_worstLayer (r : Fin (k + 1) → ℝ) : Fin (k + 1) := worstIndex r


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layer-wise rule [1, Def. 4.6]: every neuron of the worst-ranked of
`k + 1` layers moves up an order. -/
noncomputable def Schedule.refineWorst (sch : Schedule) (r : Fin (k + 1) → ℝ) : Schedule :=
  Schedule.refineLayer sch (aux_worstLayer r)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
