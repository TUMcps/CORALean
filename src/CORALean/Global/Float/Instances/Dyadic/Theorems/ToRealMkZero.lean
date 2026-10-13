import CORALean.Global.Float.Instances.Dyadic.Dyadic

/-!
# A zero mantissa reads as zero at every scale

Any exponent, since a zero mantissa reads as zero regardless of the scale it
is read at — what `SoundFloatArithmetic.toReal_zero` needs from `Dyadic`.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_mk_zero (e : ℤ) : toReal (⟨0, e⟩ : Dyadic p) = 0 := by
  rw [toReal_def, Int.cast_zero, zero_mul]

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
