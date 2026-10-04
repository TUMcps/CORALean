import CORALean.ContSet.Interval.Real.Interval

/-!
# `ConPolyZono.unitBox`

The factor box `[-1,1]ᵖ`, which `rescale` contracts.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.unitBox (p : ℕ) : Interval (Vec ℝ p) where
  inf := fun _ => -1
  sup := fun _ => 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
