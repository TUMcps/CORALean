module

public import CORALean.ContSet.Conversion.Real.SpectraShadow_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope

@[expose] public section

/-!
# A spectrahedral shadow as a conZonotope — the construction

`SpectraShadow.conZonotope` is the construction; `SpectraShadow_to_ConZonotope` states and proves
what it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def SpectraShadow.conZonotope (S : SpectraShadow α) : ConZonotope α :=
  S.zonotope.conZonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
