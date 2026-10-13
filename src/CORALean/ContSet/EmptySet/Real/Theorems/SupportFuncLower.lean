import CORALean.ContSet.EmptySet.Real.Operations.SupportFunc
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# The lower support function of the empty set

CORA's `supportFunc_(O,dir,'lower')` is `Inf`: the infimum of `c` over no point in
`EReal`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.supportFunc_lower (E : EmptySet n) (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    ⨅ x ∈ construct E, ((c x : ℝ) : EReal) = ⊤ := by
  change ⨅ x ∈ (∅ : Set (Vec ℝ n)), ((c x : ℝ) : EReal) = ⊤
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
