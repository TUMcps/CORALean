module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopePosSemidefSpectraShadowIff

@[expose] public section

/-!
# A zonotope as a spectrahedral shadow

`Zonotope.spectraShadow_exact`: its `spectraShadow` is exactly it.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* zonotope equals its spectrahedral shadow
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.spectraShadow_exact (Z : Zonotope α) :
    Z.construct = Z.spectraShadow.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨β, hβ, rfl⟩
    exact ⟨β, (Zonotope.posSemidef_spectraShadow_iff Z β).mpr hβ, rfl⟩
  · rintro _ ⟨β, hβ, rfl⟩
    exact ⟨β, (Zonotope.posSemidef_spectraShadow_iff Z β).mp hβ, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
