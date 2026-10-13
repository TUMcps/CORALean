module

public import CORALean.Global.Float.Instances.FixedPoint.FixedPoint

@[expose] public section

/-!
# A zero mantissa reads as zero at every digit count

Any digit count, since a zero mantissa reads as zero regardless of the scale
it is read at -- what `SoundFloatArithmetic.toReal_zero` needs from
`FixedPoint`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_mk_zero (d : ℕ) : toReal (⟨0, d⟩ : FixedPoint f) = 0 := by
  rw [toReal_def, Int.cast_zero, zero_div]

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
