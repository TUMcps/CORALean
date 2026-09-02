import CORALean.ContSet.ConZonotope.Operations.Reduce
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter
import CORALean.ContSet.ConZonotope.Theorems.ZonotopeOuter

/-!
# `ConZonotope.reduce` over-approximates

Above the order it is the zonotope's `reduce` composed with forgetting the
constraints, both enclosures; at or below it, the identity.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

theorem ConZonotope.reduce_outer (C : ConZonotope (Vec ℝ n)) (o : ℕ) :
    C.construct ⊆ (C.reduce o).construct := by
  unfold ConZonotope.reduce
  split_ifs with hlt
  · rw [← Zonotope.conZonotope_exact]
    exact subset_trans (ConZonotope.zonotope_outer C) (Zonotope.reduce_outer C.zonotope o)
  · exact subset_rfl

end CORALean.Real
