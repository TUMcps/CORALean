module

public import CORALean.ContSet.Interval.Float.Operations.QuadMapCora
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapTriOuter
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `Interval.quadMapCora` over-approximates the quadratic map

The box's points are its zonotope's (`zonotope_contains`), the zonotope's quadratic map is
enclosed by `Zonotope.quadMapTri_outer`, and the result is enclosed by its box
(`interval_contains`).

## Inputs
* `Q` – family of float quadratic form matrices
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the quadratic map image of `I` lies in the result box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.quadMapCora_outer (Q : Fin m → Mat 𝕋 n n) (I : Interval (Vec 𝕋 n)) :
    Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' I.toSet
      ⊆ (I.quadMapCora Q).toSet :=
  (Set.image_mono I.zonotope_contains).trans
    ((Zonotope.quadMapTri_outer Q I.zonotope).trans
      (Zonotope.quadMapTri Q I.zonotope).interval_contains)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
