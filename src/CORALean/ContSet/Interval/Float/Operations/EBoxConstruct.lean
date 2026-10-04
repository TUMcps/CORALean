import CORALean.ContSet.Interval.Float.Operations.EBox

/-!
# `Interval.EBox.construct`, over a floating-point scalar

The points whose every coordinate lies above each stored lower bound and below each stored upper
bound.
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

def Interval.EBox.construct (B : Interval.EBox 𝕋 n) : Set (Vec ℝ n) :=
  {x | ∀ i, (∀ l, B.lo i = some l → toReal l ≤ x i) ∧ (∀ u, B.hi i = some u → x i ≤ toReal u)}

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
