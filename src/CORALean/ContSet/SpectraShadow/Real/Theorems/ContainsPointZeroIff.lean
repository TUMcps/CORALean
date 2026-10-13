import CORALean.ContSet.SpectraShadow.Real.Operations.ContainsPoint

/-!
# `SpectraShadow.containsPoint_zero_iff`

At tolerance `0` the point test is membership, exactly: the slack is forced to `0`.
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

theorem SpectraShadow.containsPoint_zero_iff (S : SpectraShadow α) (p : α) :
    S.containsPoint p 0 ↔ p ∈ S.construct := by -- --- PROOF ---
  constructor
  · -- the slack is zero, so the inequality is the set's own
    rintro ⟨β, s, hp, hs, hM⟩
    have h0 : s = 0 := funext fun i => abs_nonpos_iff.mp (hs i)
    subst h0
    rw [show Matrix.diagonal (0 : Fin S.k → ℝ) = 0 from Matrix.diagonal_zero, add_zero] at hM
    exact ⟨β, hM, hp.symm⟩
  · -- a member is tested with the zero slack
    rintro ⟨β, hβ, rfl⟩
    refine ⟨β, 0, rfl, fun i => by simp, ?_⟩
    rw [show Matrix.diagonal (0 : Fin S.k → ℝ) = 0 from Matrix.diagonal_zero, add_zero]
    exact hβ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
