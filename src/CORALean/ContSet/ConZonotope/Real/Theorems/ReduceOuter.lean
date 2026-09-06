import CORALean.ContSet.ConZonotope.Real.Operations.Reduce
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope

/-!
# `ConZonotope.reduce` over-approximates

Above the order it is the zonotope's `reduce` composed with forgetting the
constraints, both enclosures; at or below it, the identity.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduce_outer (C : ConZonotope (Vec ℝ n)) (o : ℕ) :
    C.construct ⊆ (C.reduce o).construct := by -- --- PROOF ---
  unfold ConZonotope.reduce
  split_ifs with hlt
  · rw [← Zonotope.conZonotope_exact]
    exact subset_trans (ConZonotope.zonotope_outer C) (Zonotope.reduce_outer C.zonotope o)
  · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
