module

public import CORALean.ContSet.Conversion.Float.Operations.ZonoBundle_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Theorems.ConZonotopeConPolyZonoContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonoBundleConZonotopeAllContains

@[expose] public section

/-!
# A float bundle lies in its constrained polynomial zonotope

`conPolyZono(conZonotope(zB))`: the intersected constrained zonotope holds the bundle
(`ZonoBundle.conZonotopeAll_contains`), and its constrained polynomial zonotope holds that.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float bundle lies in CORA's `conPolyZono(conZonotope(zB))`. -/
theorem ZonoBundle.conPolyZonoAll_contains (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) :
    zB.construct ⊆ (zB.conPolyZonoAll hk).construct :=
  subset_trans (zB.conZonotopeAll_contains hk) (ConZonotope.conPolyZono_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
