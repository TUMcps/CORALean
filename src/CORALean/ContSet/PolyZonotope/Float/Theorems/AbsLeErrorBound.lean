import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent

/-!
# One generator per coordinate reaches every point of a box
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- One generator per coordinate reaches every point of the box. -/
theorem PolyZonotope.abs_le_errorBound {I : Interval 𝕋 n} {e : Vec ℝ n}
    (he : e ∈ I.construct) (i : Fin n) : |e i| ≤ toReal (PolyZonotope.errorBound I i) := by
  have hlo : toReal (I.inf i) ≤ e i := (he i).1
  have hhi : e i ≤ toReal (I.sup i) := (he i).2
  have hmax : toReal (PolyZonotope.errorBound I i)
      = max |toReal (I.inf i)| |toReal (I.sup i)| := by
    rw [PolyZonotope.errorBound, toReal_maximum, toReal_absolute, toReal_absolute]
  rw [hmax, abs_le]
  constructor
  · exact le_trans (neg_le_neg (le_max_left _ _)) (le_trans (neg_abs_le _) hlo)
  · exact le_trans hhi (le_trans (le_abs_self _) (le_max_right _ _))

end CORALean.Float
