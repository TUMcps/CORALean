module

public import CORALean.NN.Graph.Operations.BallEnum

@[expose] public section

/-!
# The enumeration never repeats a node

`ballEnum` is `Finset.orderEmbOfFin` coerced to a function, and an order
embedding is injective on the nose — `RelEmbedding.injective` closes it.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- `ballEnum` sends distinct indices to distinct nodes. -/
theorem GNN.ballEnum_injective {N : ℕ} (A : Mat ℝ N N) (v : Fin N) (L : ℕ) :
    Function.Injective (GNN.ballEnum A v L) :=
  ((GNN.ball A v L).orderEmbOfFin rfl).injective

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
