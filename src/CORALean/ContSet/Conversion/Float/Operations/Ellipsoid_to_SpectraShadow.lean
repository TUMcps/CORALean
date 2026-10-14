module

public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_SpectraShadow
public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# An ellipsoid as a spectrahedral shadow, over a floating-point scalar
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.spectraShadow (E : Ellipsoid 𝕋 n) : SpectraShadow 𝕋 (Vec 𝕋 n) where
  k := E.k + 1
  m := E.k
  A₀ := fun p q => if p = q then one else zero
  A := fun i p q => if (p = 0 ∧ q = i.succ) ∨ (p = i.succ ∧ q = 0) then one else zero
  c := E.c
  G := fun j i => E.G i j
  I_error := E.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
