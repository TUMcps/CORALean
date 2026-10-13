module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Neg

@[expose] public section

/-!
# Negation is exact

Touching the mantissa alone, which is what `SoundFloatArithmetic.toReal_neg`
needs from `Dyadic`.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_neg (d : Dyadic p) : toReal (neg d) = -toReal d := by
  rw [toReal_def, toReal_def, neg, Int.cast_neg, neg_mul]

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
