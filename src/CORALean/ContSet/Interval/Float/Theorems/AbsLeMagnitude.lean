import CORALean.ContSet.Interval.Float.Operations.Magnitude

/-!
# A point of an interval vector is within its magnitude of the origin
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.abs_le_magnitude {I : Interval (Vec 𝕋 n)} {b : Vec ℝ n} (hb : b ∈ I.construct)
    (i : Fin n) : |b i| ≤ toReal (I.magnitude i) := by
  have h : toReal (I.inf i) ≤ b i ∧ b i ≤ toReal (I.sup i) := hb i
  rw [Interval.magnitude, toReal_maximum, toReal_absolute, toReal_absolute]
  exact abs_le_max_abs_abs h.1 h.2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
