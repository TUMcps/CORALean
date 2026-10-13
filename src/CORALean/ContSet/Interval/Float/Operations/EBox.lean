import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.EBox`, over a floating-point scalar

A box with possibly infinite ends, for the results (`Inf`, `lift_`, `dirac`) a floating-point
scalar cannot store: a bound is a float, or `none` for `-∞` (lower) or `∞` (upper).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Interval.EBox (𝕋 : Type) (n : ℕ) where
  lo : Fin n → Option 𝕋
  hi : Fin n → Option 𝕋

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
