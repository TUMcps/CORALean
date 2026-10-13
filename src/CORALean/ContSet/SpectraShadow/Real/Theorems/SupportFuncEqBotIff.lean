import CORALean.ContSet.SpectraShadow.Real.Theorems.LeSupportFuncOfMem

/-!
# `SpectraShadow.supportFunc_eq_bot_iff`

The support function is `⊥`, that of the empty set, exactly for the empty set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.supportFunc_eq_bot_iff (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ) :
    S.supportFunc c = ⊥ ↔ S.construct = ∅ := by -- --- PROOF ---
  constructor
  · -- a point would sit below `⊥`
    intro h
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    have := S.le_supportFunc_of_mem c hx
    rw [h] at this
    exact absurd (le_bot_iff.mp this) (EReal.coe_ne_bot _)
  · -- the supremum over nothing
    intro h
    simp [SpectraShadow.supportFunc, h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
