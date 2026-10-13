module

public import CORALean.ContSet.ConZonotope.Real.Operations.ReduceLift
public import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceLiftByOuter

@[expose] public section

/-!
# `ConZonotope.reduceLift` over-approximates

Above the generator count it is `reduceLiftBy_outer` at the partition Girard's rule chose
for the lifted zonotope; at or below it, the identity.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduceLift_outer (cZ : ConZonotope (Vec ℝ n)) (o : ℕ) :
    cZ.construct ⊆ (cZ.reduceLift o).construct := by -- --- PROOF ---
  unfold ConZonotope.reduceLift
  simp only []
  split_ifs with hlt
  · exact ConZonotope.reduceLiftBy_outer cZ _
  · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
