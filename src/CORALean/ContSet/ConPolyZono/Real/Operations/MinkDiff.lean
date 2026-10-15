module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Intersection
public import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
public import CORALean.ContSet.ConPolyZono.Real.Operations.OfPoint
public import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `ConPolyZono.minkDiff`

CORA's `@conPolyZono/minkDiff` with a zonotope subtrahend [1, Thm. 1], type `'exact'`: the
independent generators of the minuend become dependent ones (`dependent`), the subtrahend's
center is subtracted, and for every generator `g` of the subtrahend the set `P` is replaced by
`(P + g) ∩ (P - g)`.

For a convex minuend each step is exact, `{x | x ± g ∈ P} = {x | x + [-g, g] ⊆ P}`, and the result
is `P ⊖ Z`. For a nonconvex minuend the segment between `x - g` and `x + g` is not in `P` in
general, so CORA's `'exact'` is an outer approximation there: `minkDiff_not_inner` gives a minuend
and a zonotope for which the result is not a subset of the difference. The numeric subtrahend
(`P + (-v)`), the vertex form for a conZonotope, polytope or zonoBundle subtrahend (Lemma 1) and the
`'inner'` type are not modelled.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `cPZ₁ ⊖ Z` for a zonotope `Z`, by [1, Thm. 1]: one `(P + g) ∩ (P - g)` per generator. -/
def ConPolyZono.minkDiff (cPZ₁ : ConPolyZono (Vec ℝ n)) (Z : Zonotope (Vec ℝ n)) :
    ConPolyZono (Vec ℝ n) :=
  -- the independent generators become dependent ones
  let P₁ := cPZ₁.dependent
  -- the center is subtracted, and each generator `g` cuts `(P + g) ∩ (P - g)`
  Fin.foldl Z.h
    (fun cPZ i => (cPZ.plus (ConPolyZono.ofPoint (Z.G i))).intersection
      (cPZ.plus (ConPolyZono.ofPoint (-Z.G i))))
    (P₁.plus (ConPolyZono.ofPoint (-Z.c)))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
