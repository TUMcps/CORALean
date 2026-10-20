module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A constrained polynomial zonotope as a polynomial zonotope, over a

## Inputs
* `cPZ` – constrained polynomial zonotope

## Output
* polynomial zonotope with the same data, constraints dropped
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

def ConPolyZono.polyZonotope (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) where
  p := cPZ.p
  h := cPZ.h
  q := cPZ.qI
  c := cPZ.c
  G := cPZ.G
  E := cPZ.E
  GI := cPZ.GI
  I_error := cPZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
