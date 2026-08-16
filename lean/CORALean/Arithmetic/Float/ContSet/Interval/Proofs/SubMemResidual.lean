import CORALean.Arithmetic.Float.ContSet.Interval.API

/-!
# What is left over after storing a rounded vector

Both bounds are one directed subtraction away from the bracket the caller
already has.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.Interval.Proofs

open FloatOps SoundFloatArithmetic

variable {F : Type} [FloatOps F] [SoundFloatArithmetic F] {n : ℕ}

theorem sub_mem_residual {lo hi stored : Vec F n} {x : Vec ℝ n}
    (h : ∀ i, toReal (lo i) ≤ x i ∧ x i ≤ toReal (hi i)) :
    (fun i => x i - toReal (stored i)) ∈ (Interval.residual lo hi stored).construct := fun i =>
  ⟨le_trans (subDown_le_sub _ _) (sub_le_sub_right (h i).1 _),
   le_trans (sub_le_sub_right (h i).2 _) (sub_le_subUp _ _)⟩

end CORALean.Arithmetic.Float.Interval.Proofs
