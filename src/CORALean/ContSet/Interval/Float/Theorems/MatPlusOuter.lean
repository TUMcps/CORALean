import CORALean.ContSet.Interval.Float.Operations.MatPlus
import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.matPlus` contains the entrywise sum

`Interval.plus`'s counterpart at `Mat 𝕋 m n`: nothing about sums of sets — the
whole obligation is that each bound rounds the right way, entrywise.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.matPlus_outer (I₁ I₂ : Interval (Mat 𝕋 m n)) {M N : Mat ℝ m n}
    (hM : M ∈ I₁.construct) (hN : N ∈ I₂.construct) :
    M + N ∈ (Interval.matPlus I₁ I₂).construct := by -- --- PROOF ---
  intro q
  obtain ⟨i, j⟩ := q
  have hM' := hM (i, j)
  have hN' := hN (i, j)
  simp only [Entrywise.entry_mat] at hM' hN' ⊢
  exact ⟨le_trans (addDown_le_add _ _) (add_le_add hM'.1 hN'.1),
         le_trans (add_le_add hM'.2 hN'.2) (add_le_addUp _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
