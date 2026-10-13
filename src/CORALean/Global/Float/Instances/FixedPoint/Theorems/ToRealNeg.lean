import CORALean.Global.Float.Instances.FixedPoint.Operations.Neg

/-!
# Negation is exact

Touching the mantissa alone, which is what `SoundFloatArithmetic.toReal_neg`
needs from `FixedPoint`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_neg (x : FixedPoint f) : toReal (neg x) = -toReal x := by
  rw [toReal_def, toReal_def, neg, Int.cast_neg, neg_div]

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
