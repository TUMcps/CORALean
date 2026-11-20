module

public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapTriFiltered
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapFilterOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapTriOuter

@[expose] public section

/-!
# Float `quadMapTriFiltered` encloses the quadratic image

`quadMapTri` holds the image (`quadMapTri_outer`), and `quadMapFilter` keeps its set
(`quadMapFilter_outer`).

## Inputs
* `Q` – quadratic form per output coordinate
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the filtered quadratic map holds the quadratic image of the zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   20-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `{xᵀQ⁽ⁱ⁾x | x ∈ Z} ⊆ Z.quadMapTriFiltered Q`. -/
theorem Zonotope.quadMapTriFiltered_outer (Q : Fin m → Mat 𝕋 n n)
    (Z : Zonotope (Vec 𝕋 n)) :
    Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' Z.toSet
      ⊆ (Z.quadMapTriFiltered Q).toSet :=
  (Zonotope.quadMapTri_outer Q Z).trans (Zonotope.quadMapFilter_outer Q _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
