module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Center
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# A box as a zonotope, over a floating-point scalar

## Inputs
* `I` – interval

## Output
* radius reaching both ends from the stored center
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Far enough from the stored center to reach both ends. -/
def Interval.radiusFrom (I : Interval (Vec 𝕋 n)) : Vec 𝕋 n :=
  fun i => maximum (subUp (I.sup i) (I.center i)) (subUp (I.center i) (I.inf i))

-- the stored center, and one diagonal generator per coordinate
def Interval.zonotope (I : Interval (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := n
  c := I.center
  G := diagonalBlock I.radiusFrom
  I_error := ⟨fun _ => zero, fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
