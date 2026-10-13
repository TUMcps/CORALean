import CORALean.ContSet.Conversion.Real.SpectraShadow_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope

/-!
# A spectrahedral shadow as a conZonotope

CORA's `conZonotope(SpS)` is `conZonotope(zonotope(SpS))`. The zonotope encloses a shadow with
bounded base spectrahedron (`SpectraShadow.zonotope_contains`), and the conversion of a
zonotope loses nothing (`Zonotope.conZonotope_exact`), so this is an outer
approximation too, not an equality.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


noncomputable def SpectraShadow.conZonotope (S : SpectraShadow α) : ConZonotope α :=
  S.zonotope.conZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.conZonotope_contains (S : SpectraShadow α) (hb : S.base.isBounded) :
    S.construct ⊆ S.conZonotope.construct := by
  rw [SpectraShadow.conZonotope, ← Zonotope.conZonotope_exact]
  exact S.zonotope_contains hb

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
