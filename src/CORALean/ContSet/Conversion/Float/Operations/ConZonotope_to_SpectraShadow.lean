module

public import CORALean.ContSet.Conversion.Float.HPolytope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A constrained zonotope as a spectrahedral shadow, over a floating-point scalar — the construction

`ConZonotope.spectraShadow` is the construction; `ConZonotope_to_SpectraShadow` states and proves
what it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.spectraShadow (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) where
  k := (cZ.h + cZ.h) + (cZ.P.m + (cZ.P.me + cZ.P.me))
  m := cZ.h
  A₀ := blockDiag FloatOps.zero cZ.zonotope.spectraShadow.A₀ cZ.P.spectraShadow.A₀
  A := fun j => blockDiag FloatOps.zero (cZ.zonotope.spectraShadow.A j) (cZ.P.spectraShadow.A j)
  c := cZ.c
  G := cZ.G
  I_error := cZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
