module

public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Theorems.ConZonotopeConPolyZonoContains
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeConZonotopeContains

@[expose] public section

/-!
# A float halfspace description lies in its constrained polynomial zonotope

`conPolyZono(conZonotope(P))`: the float constrained zonotope holds the polytope
(`HPolytope.conZonotope_contains`), and its constrained polynomial zonotope holds it in turn.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float polytope lies in CORA's `conPolyZono(conZonotope(P))`. -/
theorem HPolytope.conPolyZono_contains (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.conPolyZono up lo).construct := by -- --- PROOF ---
  -- `conZonotope(P)` holds `P`
  have h₁ := HPolytope.conZonotope_contains up lo
  -- and its constrained polynomial zonotope holds that
  have h₂ := ConZonotope.conPolyZono_contains (HPolytope.conZonotope up lo)
  exact subset_trans h₁ h₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
