module

public import CORALean.ContSet.Conversion.Real.SpectraShadow_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# A spectrahedral shadow as a polyZonotope — the construction

`SpectraShadow.polyZonotope` is the construction; `SpectraShadow_to_PolyZonotope` states and proves
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

noncomputable def SpectraShadow.polyZonotope (S : SpectraShadow α) : PolyZonotope α :=
  S.zonotope.polyZonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
