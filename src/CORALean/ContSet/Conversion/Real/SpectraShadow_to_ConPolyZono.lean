module

public import CORALean.ContSet.Conversion.Real.SpectraShadow_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ConPolyZono

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
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


noncomputable def SpectraShadow.conPolyZono (S : SpectraShadow α) : ConPolyZono α :=
  S.zonotope.conPolyZono


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.conPolyZono_contains (S : SpectraShadow α) (hb : S.base.isBounded) :
    S.construct ⊆ S.conPolyZono.construct := by
  rw [SpectraShadow.conPolyZono, ← Zonotope.conPolyZono_exact]
  exact S.zonotope_contains hb

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
