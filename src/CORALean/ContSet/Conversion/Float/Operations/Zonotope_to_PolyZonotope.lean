module

public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialIdentE
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A zonotope as a polynomial zonotope, over a floating-point scalar

## Inputs
* `Z` – zonotope

## Output
* polynomial zonotope of the zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.polyZonotope (Z : Zonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) where
  p := Z.h
  h := Z.h
  q := 0
  c := Z.c
  G := Z.G
  E := Real.PolyZonotope.identE Z.h
  GI := Fin.elim0
  I_error := Z.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
