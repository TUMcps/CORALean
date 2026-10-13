import CORALean.ContSet.SpectraShadow.Real.Theorems.LeSupportFuncOfMem
import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncLeOfBound

/-!
# `SpectraShadow.supportFunc_ne_top_iff`

The support function is below `⊤` exactly when `c` has a real upper bound on the set.
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

theorem SpectraShadow.supportFunc_ne_top_iff (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ) :
    S.supportFunc c ≠ ⊤ ↔ ∃ M : ℝ, ∀ x ∈ S.construct, c x ≤ M := by -- --- PROOF ---
  constructor
  · -- read the value as `⊥` (any bound serves), a real (it bounds) or `⊤` (excluded)
    intro h
    induction hs : S.supportFunc c using EReal.rec with
    | bot =>
      refine ⟨0, fun x hx => ?_⟩
      have := S.le_supportFunc_of_mem c hx
      rw [hs] at this
      exact absurd (le_bot_iff.mp this) (EReal.coe_ne_bot _)
    | coe r =>
      refine ⟨r, fun x hx => ?_⟩
      have := S.le_supportFunc_of_mem c hx
      rw [hs] at this
      exact EReal.coe_le_coe_iff.mp this
    | top => exact absurd hs h
  · -- a real bound puts the supremum below it
    rintro ⟨M, hM⟩
    exact ne_top_of_le_ne_top (EReal.coe_ne_top M)
      (S.supportFunc_le_of_bound c ⟨M, hM⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
