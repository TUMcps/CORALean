import CORALean.ContSet.Conversion.Real.SpectraShadow_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle

/-!
# A spectrahedral shadow as a zonoBundle

CORA's `zonoBundle(SpS)` is `zonoBundle(zonotope(SpS))`. The zonotope encloses a shadow with
bounded base spectrahedron (`SpectraShadow.zonotope_contains`), and the conversion of a
zonotope loses nothing (`Zonotope.zonoBundle_exact`), so this is an outer
approximation too, not an equality.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


noncomputable def SpectraShadow.zonoBundle (S : SpectraShadow α) : ZonoBundle α :=
  S.zonotope.zonoBundle


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.zonoBundle_contains (S : SpectraShadow α) (hb : S.base.isBounded) :
    S.construct ⊆ S.zonoBundle.construct := by
  rw [SpectraShadow.zonoBundle, ← Zonotope.zonoBundle_exact]
  exact S.zonotope_contains hb

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
