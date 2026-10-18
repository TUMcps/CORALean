module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono

@[expose] public section

/-!
# A polynomial zonotope as a constrained one, over a floating-point scalar
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

def PolyZonotope.conPolyZono (pZ : PolyZonotope (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := pZ.p
  h := pZ.h
  qI := pZ.q
  m := 0
  q := 0
  c := pZ.c
  G := pZ.G
  E := pZ.E
  GI := pZ.GI
  A := fun i => i.elim0
  b := fun i => i.elim0
  b_error := fun i => i.elim0
  R := fun _ => Fin.elim0
  I_error := pZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
