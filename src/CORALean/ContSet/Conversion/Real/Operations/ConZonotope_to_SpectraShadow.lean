module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow

@[expose] public section

/-!
# A constrained zonotope as a spectrahedral shadow
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.spectraShadow (cZ : ConZonotope α) : SpectraShadow α where
  k := (cZ.h + cZ.h) + (cZ.P.m + cZ.P.me + cZ.P.me)
  m := cZ.h
  A₀ := blockDiag 0 (Zonotope.spectraShadow ⟨cZ.h, cZ.c, cZ.G⟩).A₀ cZ.P.spectraShadow.A₀
  A := fun j => blockDiag 0 ((Zonotope.spectraShadow ⟨cZ.h, cZ.c, cZ.G⟩).A j)
    (cZ.P.spectraShadow.A j)
  c := cZ.c
  G := cZ.G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
