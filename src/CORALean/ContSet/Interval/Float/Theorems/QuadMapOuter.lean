import CORALean.ContSet.Interval.Float.Operations.QuadMap
import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapOuter

/-!
# `Interval.quadMap` over-approximates the quadratic map, over a floating-point scalar

The box's points are its zonotope's (`zonotope_contains`), the zonotope's quadratic map is
enclosed by `Zonotope.quadMap_outer`, and the result is enclosed by its box
(`interval_contains`).
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.quadMap_outer (Q : Fin m → Mat 𝕋 n n) (I : Interval (Vec 𝕋 n)) :
    Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' I.construct
      ⊆ (I.quadMap Q).construct :=
  (Set.image_mono I.zonotope_contains).trans
    ((Zonotope.quadMap_outer Q I.zonotope).trans (I.zonotope.quadMap Q).interval_contains)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
