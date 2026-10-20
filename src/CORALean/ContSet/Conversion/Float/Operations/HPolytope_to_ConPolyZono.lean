module

public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotope

@[expose] public section

/-!
# A halfspace description as a constrained polynomial zonotope, over a floating-point scalar

CORA's `conPolyZono(conZonotope(P))`, as over ℝ: the float `HPolytope.conZonotope` on the box of
the support bounds, then its float constrained polynomial zonotope.

## Inputs
* none

## Hypotheses
* `up` – float upper bound per coordinate
* `lo` – float lower bound per coordinate

## Output
* constrained polynomial zonotope of the polytope
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `conPolyZono(P)`: `conPolyZono(conZonotope(P))`. -/
def HPolytope.conPolyZono (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  -- `conZonotope(P)`, the box from the support bounds
  let cZ := HPolytope.conZonotope up lo
  -- `conPolyZono(cZ)`
  cZ.conPolyZono

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
