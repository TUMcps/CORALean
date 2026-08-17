import CORALean.Arithmetic.Float.ContSet.Interval.API

/-!
# `Interval.plus` encloses the exact sum

The whole obligation, since `Arithmetic.Real` has already proved that the exact
sum contains the Minkowski sum. Nothing about sums of sets appears here — only
that each bound rounded the right way.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.Interval.Proofs

open FloatOps SoundFloatArithmetic

variable {F : Type} [FloatOps F] [SoundFloatArithmetic F] {n : ℕ}

theorem plus_outer_refines (I₁ I₂ : Interval F n) :
    (I₁.nominal.plus I₂.nominal).construct ⊆ (I₁.plus I₂).construct := by
  intro x hx i
  exact ⟨le_trans (addDown_le_add _ _) (hx i).1, le_trans (hx i).2 (add_le_addUp _ _)⟩

end CORALean.Arithmetic.Float.Interval.Proofs
