import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.ContSet.Interval.Real.Interval

/-!
# `Zonotope.IsBox`

What `representsa_(Z, 'interval', tol)` decides at tolerance `0`: the zonotope is an axis-aligned
box, the set of an `Interval`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The zonotope is an axis-aligned box. -/
def Zonotope.IsBox (Z : Zonotope (Vec ℝ n)) : Prop :=
  ∃ I : Interval (Vec ℝ n), Z.construct = I.construct


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
