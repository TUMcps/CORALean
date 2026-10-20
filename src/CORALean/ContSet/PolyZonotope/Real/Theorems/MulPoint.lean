module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Mul
public import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinPoint

@[expose] public section

/-!
# `mul`'s point is the product of the two points

`bilin_point` at the entrywise product, which is what `mul` is. Shared by
`MulExact` and `EvalPolyExact`, which both need it and cannot import one
another: `mul_exact` states it over the sets, `evalPoly_exact`'s recursion over
the sets' points at each Horner step.

The statement reads as `*` rather than as `hadamardLin` because at `Vec` the
two are the same term: a coordinate is an application there, so `ofEntry` and
`entry` are both the identity.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `a` – factor values

## Hypotheses
* `hp` – both have the same factor count

## Conclusion
* the point is the product of the two points
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mul`'s point, read off `bilin`'s rather than `construct`: a product of the
two points, `pZ₂` read at `pZ₁`'s factors through `Fin.cast`. -/
theorem PolyZonotope.mul_point (pZ₁ pZ₂ : PolyZonotope (Vec ℝ n)) (hp : pZ₁.p = pZ₂.p)
    (a : Fin pZ₁.p → ℝ) :
    (pZ₁.mul pZ₂ hp).point a = pZ₁.point a * pZ₂.point (fun k => a (Fin.cast hp.symm k)) :=
  PolyZonotope.bilin_point Entrywise.hadamardLin pZ₁ pZ₂ hp a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
