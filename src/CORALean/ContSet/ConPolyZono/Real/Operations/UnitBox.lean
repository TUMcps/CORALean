module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `ConPolyZono.unitBox`

The factor box `[-1,1]ᵖ`, which `rescale` contracts.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.unitBox (p : ℕ) : Interval (Vec ℝ p) where
  inf := fun _ => -1
  sup := fun _ => 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
