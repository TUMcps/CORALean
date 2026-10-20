module

public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadEval
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep
public import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinPoint

@[expose] public section

/-!
# `quadMapDep`'s point is the quadratic form at the point

`bilin_point` at `quadBilin`, one set paired with itself: the image of the factor vector `a` is
the quadratic form evaluated at the point `a` picks out (`quadEval Q x` is `quadBilin Q x x`
definitionally). The point-level companion to `quadMapDep_exact`, and what a
*dependency-preserving* abstraction error is stated against: it says which factors carry the
second-order term. Only the dependent block is named, so no hypothesis on `q` appears;
`dependent` is what brings the independent generators in.

## Inputs
* `Q` – family of quadratic form matrices
* `pZ` – polynomial zonotope
* `a` – factor values

## Hypotheses
* none

## Conclusion
* the point is the quadratic map of the point
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The second-order term as a polynomial in the very factors `pZ` is written
in, rather than as an enclosure of it. -/
theorem PolyZonotope.quadMapDep_point (Q : Fin m → Mat ℝ n n) (pZ : PolyZonotope (Vec ℝ n))
    (a : Fin pZ.p → ℝ) : (quadMapDep Q pZ).point a = quadEval Q (pZ.point a) :=
  PolyZonotope.bilin_point (PolyZonotope.quadBilin Q) pZ pZ rfl a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
