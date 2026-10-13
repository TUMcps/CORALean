import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.smul`

Scaling a box by a real, entrywise: `[a, b]` becomes
`[min (c * a) (c * b), max (c * a) (c * b)]`, so a negative `c` swaps which
product is the low corner instead of carrying `c • inf` there blindly.

`exp` of an interval matrix needs this for its Taylor term
`t ^ i / i ! • matPow A i`; the enclosure is `Theorems/SmulOuter`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.smul (c : ℝ) (I : Interval α) : Interval α where
  inf := ofEntry fun i => min (c * entry I.inf i) (c * entry I.sup i)
  sup := ofEntry fun i => max (c * entry I.inf i) (c * entry I.sup i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
