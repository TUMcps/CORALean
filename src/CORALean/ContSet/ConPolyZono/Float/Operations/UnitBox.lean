import CORALean.ContSet.Interval.Float.Interval

/-!
# `ConPolyZono.unitBox` over a floating-point scalar

The factor box `[-1,1]ᵖ` with which CORA's `@conPolyZono/rescale` starts, stored as floats:
`-1` and `1` are exact in the scalar, so the box is the exact layer's.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.unitBox (𝕋 : Type) [FloatOps 𝕋] (p : ℕ) : Interval (Vec 𝕋 p) where
  inf := fun _ => neg one
  sup := fun _ => one

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
