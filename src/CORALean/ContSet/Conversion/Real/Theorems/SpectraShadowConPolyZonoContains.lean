module

public import CORALean.ContSet.Conversion.Real.Theorems.SpectraShadowZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeConPolyZonoExact
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.SpectraShadow_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeConPolyZonoExact

@[expose] public section

/-!
# A spectrahedral shadow as a conPolyZono

CORA's `conPolyZono(SpS)` is `conPolyZono(zonotope(SpS))`. The zonotope encloses a shadow with
bounded base spectrahedron (`SpectraShadow.zonotope_contains`), and the conversion of a
zonotope loses nothing (`Zonotope.conPolyZono_exact`), so this is an outer
approximation too, not an equality.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.conPolyZono_contains (S : SpectraShadow α) (hb : S.base.isBounded) :
    S.construct ⊆ S.conPolyZono.construct := by
  rw [SpectraShadow.conPolyZono, ← Zonotope.conPolyZono_exact]
  exact S.zonotope_contains hb

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
