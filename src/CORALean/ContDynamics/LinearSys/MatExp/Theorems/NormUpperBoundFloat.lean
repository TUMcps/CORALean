import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
import CORALean.ContSet.Interval.Real.Operations.AbsMax
import Mathlib.Analysis.Matrix.Normed

/-!
# `MatExp.normUpperBound` bounds the dominating matrix's `l∞` operator norm

Row by row: `sum_abs_le_radius` bounds a row sum of the stored entries, which
read back as `A.nominal.absMax`'s own row exactly (`toReal_maximum`/
`toReal_absolute`); `le_maximumOver` then takes the row to the matrix bound, and
the outer `maximum zero` is where nonnegativity comes from, unconditionally.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_normUpperBound_nonneg (A : Interval (Mat 𝕋 n n)) :
    0 ≤ toReal (MatExp.normUpperBound A) := by
  rw [MatExp.normUpperBound, toReal_maximum, toReal_zero]
  exact le_max_left _ _

-- the nested `Entrywise`/`RealImage`/`toReal` unfolding through `set` costs extra defeq checking
set_option maxHeartbeats 1000000 in
theorem aux_row_le_normUpperBound (A : Interval (Mat 𝕋 n n)) (i : Fin n) :
    (∑ j, A.nominal.absMax i j) ≤ toReal (MatExp.normUpperBound A) := by -- --- PROOF ---
  set d : Mat 𝕋 n n := fun i j => maximum (absolute (A.inf i j)) (absolute (A.sup i j)) with hd
  have heq : ∀ j, |toReal (d i j)| = A.nominal.absMax i j := fun j => by
    simp only [hd, toReal_maximum, toReal_absolute]
    exact abs_of_nonneg (le_max_of_le_left (abs_nonneg _))
  calc ∑ j, A.nominal.absMax i j
      = ∑ j, |toReal (d i j)| := Finset.sum_congr rfl fun j _ => (heq j).symm
    _ ≤ toReal (radius d i) := sum_abs_le_radius i
    _ ≤ toReal (maximumOver (radius d)) := le_maximumOver _ i
    _ ≤ toReal (MatExp.normUpperBound A) := by
        rw [MatExp.normUpperBound, toReal_maximum, toReal_zero]
        exact le_max_right _ _


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.norm_absMax_le_normUpperBound (A : Interval (Mat 𝕋 n n)) :
    ‖A.nominal.absMax‖ ≤ toReal (MatExp.normUpperBound A) := by -- --- PROOF ---
  have hnn := aux_normUpperBound_nonneg A
  have hNN : ‖A.nominal.absMax‖₊ ≤ (toReal (MatExp.normUpperBound A)).toNNReal := by
    rw [Matrix.linfty_opNNNorm_def, Finset.sup_le_iff]
    intro i _
    have heq : (∑ j, A.nominal.absMax i j).toNNReal = ∑ j, ‖A.nominal.absMax i j‖₊ :=
      (Real.toNNReal_sum_of_nonneg fun j _ => le_max_of_le_left (abs_nonneg _)).trans
        (Finset.sum_congr rfl fun j _ =>
          Real.toNNReal_eq_nnnorm_of_nonneg (le_max_of_le_left (abs_nonneg _)))
    rw [← heq]
    exact Real.toNNReal_le_toNNReal (aux_row_le_normUpperBound A i)
  calc ‖A.nominal.absMax‖ = (‖A.nominal.absMax‖₊ : ℝ) := (coe_nnnorm _).symm
    _ ≤ ((toReal (MatExp.normUpperBound A)).toNNReal : ℝ) := by exact_mod_cast hNN
    _ = toReal (MatExp.normUpperBound A) := Real.coe_toNNReal _ hnn

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
