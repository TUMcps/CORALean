module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# A zonotope as a spectrahedral shadow — the construction

`Zonotope.spectraShadow` is the construction; `Zonotope_to_SpectraShadow` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.spectraShadow (Z : Zonotope α) : SpectraShadow α where
  k := Z.h + Z.h
  m := Z.h
  A₀ := blockDiag 0 1 1
  A := fun j => blockDiag 0 (diagonal (Pi.single j 1)) (diagonal (Pi.single j (-1)))
  c := Z.c
  G := Z.G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
