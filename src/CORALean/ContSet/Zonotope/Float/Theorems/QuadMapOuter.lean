module

public import CORALean.ContSet.Zonotope.Float.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapOuter

@[expose] public section

/-!
# `Zonotope.quadMap` over-approximates the quadratic map, over a floating-point scalar

A zonotope's points are the polynomial zonotope's (`polyZonotope_contains`), the polynomial
zonotope's quadratic map is enclosed by `PolyZonotope.quadMap_outer`, and its points are the
zonotope's (`zonotope_contains`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.quadMap_outer (Q : Fin m → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) :
    Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' Z.construct
      ⊆ (Z.quadMap Q).construct :=
  (Set.image_mono Z.polyZonotope_contains).trans
    ((PolyZonotope.quadMap_outer Q Z.polyZonotope).trans
      (PolyZonotope.quadMap Q Z.polyZonotope).zonotope_contains)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
