import CORALean.ContSet.Interval.Float.Interval
import Mathlib.Order.Interval.Set.Defs

/-!
# `Interval.stlInterval`, over a floating-point scalar

CORA's `@interval/stlInterval`: the one-dimensional box as an STL time interval `[inf, sup]`,
closed at both ends, as the set of times the stored floats denote (no `stlInterval` class is in
the tree).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.stlInterval (I : Interval (Vec 𝕋 1)) : Set ℝ :=
  Set.Icc (toReal (I.inf 0)) (toReal (I.sup 0))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
