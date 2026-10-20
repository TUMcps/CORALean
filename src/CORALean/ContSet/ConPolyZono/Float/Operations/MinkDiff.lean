module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Intersection
public import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
public import CORALean.ContSet.ConPolyZono.Float.Operations.Dependent
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.minkDiff` over a floating-point scalar

CORA's `@conPolyZono/minkDiff` with a zonotope subtrahend [1, Thm. 1], type `'exact'`, on the
stored floats: the minuend made `dependent`, the subtrahend's center subtracted, and for every
generator `g` the set `P` replaced by `(P + g) ∩ (P - g)`. Each translate is the float `plus`
with the point `±g` (negation is exact, the center's rounding goes into the error box) and each
cut the float `intersection`, both outer, so the result is outer. The subtrahend's error box is
not subtracted: the difference is taken with its nominal part, which holds the float zonotope
when that box holds `0`.

## Inputs
* `cPZ₁` – minuend
* `Z` – zonotope subtrahend

## Output
* enclosure of the Minkowski difference

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `cPZ₁ ⊖ Z` for a zonotope `Z`, by [1, Thm. 1]: one `(P + g) ∩ (P - g)` per generator. -/
def ConPolyZono.minkDiff (cPZ₁ : ConPolyZono 𝕋 (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n)) : ConPolyZono
    𝕋 (Vec 𝕋 n) :=
  -- a float vector as a one-point set
  let pt : Vec 𝕋 n → ConPolyZono 𝕋 (Vec 𝕋 n) := fun w => (Zonotope.point w).conPolyZono
  -- the independent generators become dependent ones
  let P₁ := cPZ₁.dependent
  -- the center is subtracted, and each generator `g` cuts `(P + g) ∩ (P - g)`
  Fin.foldl Z.h
    (fun cPZ i => (cPZ.plus (pt (Z.G i))).intersection
      (cPZ.plus (pt (-(Z.G i)))))
    (P₁.plus (pt (-Z.c)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
