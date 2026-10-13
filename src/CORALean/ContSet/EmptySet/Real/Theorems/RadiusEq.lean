import CORALean.ContSet.EmptySet.Real.Operations.Radius
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# `EmptySet.radius` is the radius of the set

The radius of a set is the supremum of the norms of its points; over no point that supremum is
`0`, CORA's value.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

open ContSet in
theorem EmptySet.radius_eq (E : EmptySet n) :
    ⨆ x ∈ construct E, (‖x‖₊ : ENNReal) = E.radius := by
  change ⨆ x ∈ (∅ : Set (Vec ℝ n)), (‖x‖₊ : ENNReal) = 0
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
