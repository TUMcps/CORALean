module

public import CORALean.ContSet.ZonoBundle.Float.Operations.QuadMapCora
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapTriOuter
public import CORALean.ContSet.SetIntersection.Theorems.MemberwiseOuter

@[expose] public section

/-!
# `ZonoBundle.quadMapCora` over-approximates the quadratic image

The image of the intersection lies in the image of each member, and each member's image lies in
the member `Zonotope.quadMapTri` returns (`SetIntersection.memberwise_outer`).

## Inputs
* `Q` – quadratic form matrices
* `zB` – float zonotope bundle

## Hypotheses
* none

## Conclusion
* the quadratic image of `zB` lies in the bundle `zB.quadMapCora Q`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       21-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.quadMapCora_outer (Q : Fin m → Mat 𝕋 n n)
    (zB : ZonoBundle (Vec 𝕋 n)) :
    Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' zB.toSet
      ⊆ (zB.quadMapCora Q).toSet := by
  refine SetIntersection.memberwise_outer
    (Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' ·) Set.monotone_image fun i => ?_
  exact ⟨i, Zonotope.quadMapTri_outer Q (zB.Z i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
