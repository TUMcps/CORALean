import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.minus`

CORA's `@interval/minus` at two intervals: `[a, b] - [c, d] = [a - d, b - c]`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.minus (I₁ I₂ : Interval α) : Interval α where
  inf := I₁.inf - I₂.sup
  sup := I₁.sup - I₂.inf

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
