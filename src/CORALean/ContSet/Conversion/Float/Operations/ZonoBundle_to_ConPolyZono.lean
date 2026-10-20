module

public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Operations.ZonoBundle_to_ConZonotope

@[expose] public section

/-!
# A zonotope bundle as a constrained polynomial zonotope, as CORA's `conPolyZono(zB)`

`@zonoBundle/conPolyZono.m` is `conPolyZono(conZonotope(zB))`: the members' constrained zonotopes
intersected in order (`ZonoBundle.conZonotopeAll`, CORA's `and_(.., 'exact')`), then read as a
constrained polynomial zonotope. A bundle with no members is CORA's empty object, which a Lean
bundle (the whole space) is not, so at least one member is asked for.

## Inputs
* `zB` – zonotope bundle

## Hypotheses
* `hk` – bundle is nonempty

## Output
* constrained polynomial zonotope of the bundle
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `conPolyZono(zB)`: `conPolyZono(conZonotope(zB))`. -/
def ZonoBundle.conPolyZonoAll (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) :
    ConPolyZono 𝕋 (Vec 𝕋 n) :=
  -- `conZonotope(zB)`: the members intersected in order
  let cZ := zB.conZonotopeAll hk
  -- `conPolyZono(cZ)`
  cZ.conPolyZono

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
