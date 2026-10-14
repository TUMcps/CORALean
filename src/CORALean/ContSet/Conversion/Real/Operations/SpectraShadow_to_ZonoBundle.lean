module

public import CORALean.ContSet.Conversion.Real.SpectraShadow_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle

@[expose] public section

/-!
# A spectrahedral shadow as a zonoBundle — the construction

`SpectraShadow.zonoBundle` is the construction; `SpectraShadow_to_ZonoBundle` states and proves what
it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def SpectraShadow.zonoBundle (S : SpectraShadow α) : ZonoBundle α :=
  S.zonotope.zonoBundle

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
