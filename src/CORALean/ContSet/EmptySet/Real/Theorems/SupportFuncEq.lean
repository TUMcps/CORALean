module

public import CORALean.ContSet.EmptySet.Real.Operations.SupportFunc
public import CORALean.ContSet.EmptySet.Real.Instances

@[expose] public section

/-!
# `EmptySet.supportFunc` is the supremum

`-Inf`, CORA's value for the upper support function of the empty set, is the supremum of
`c` over no point in `EReal`. This is the sense in which the convention is the right
one; `SupportBound.ofEmpty` is the same fact over `ℝ`, every number bounding `∅`.
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

theorem EmptySet.supportFunc_eq (E : EmptySet n) (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    E.supportFunc c = ⨆ x ∈ construct E, ((c x : ℝ) : EReal) := by
  change (⊥ : EReal) = ⨆ x ∈ (∅ : Set (Vec ℝ n)), ((c x : ℝ) : EReal)
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
