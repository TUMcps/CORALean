module

public import CORALean.ContSet.Conversion.Real.SpectraShadow_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.SpectraShadow_to_PolyZonotope

@[expose] public section

/-!
# A spectrahedral shadow as a polyZonotope

CORA's `polyZonotope(SpS)` is `polyZonotope(zonotope(SpS))`. The zonotope encloses a shadow with
bounded base spectrahedron (`SpectraShadow.zonotope_contains`), and the conversion of a
zonotope loses nothing (`Zonotope.polyZonotope_exact`), so this is an outer
approximation too, not an equality.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.polyZonotope_contains (S : SpectraShadow α) (hb : S.base.isBounded) :
    S.construct ⊆ S.polyZonotope.construct := by
  rw [SpectraShadow.polyZonotope, ← Zonotope.polyZonotope_exact]
  exact S.zonotope_contains hb

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
