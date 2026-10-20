module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A box as a polynomial zonotope, over a floating-point scalar

## Inputs
* `I` – interval

## Output
* polynomial zonotope of the box
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.polyZonotope (I : Interval (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) where
  p := 0
  h := 0
  q := 0
  c := fun _ => zero
  G := Fin.elim0
  E := fun _ => Fin.elim0
  GI := Fin.elim0
  I_error := I

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
