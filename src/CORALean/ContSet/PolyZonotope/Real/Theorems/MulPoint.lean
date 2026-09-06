import CORALean.ContSet.PolyZonotope.Real.Operations.Mul
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinPoint

/-!
# `mul`'s point is the product of the two points

`bilin_point` at the entrywise product, which is what `mul` is. Shared by
`MulExact` and `EvalPolyExact`, which both need it and cannot import one
another: `mul_exact` states it over the sets, `evalPoly_exact`'s recursion over
the sets' points at each Horner step.

The statement reads as `*` rather than as `hadamardLin` because at `Vec` the
two are the same term: a coordinate is an application there, so `ofEntry` and
`entry` are both the identity.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mul`'s point, read off `bilin`'s rather than `construct`: a product of the
two points, `S₂` read at `S₁`'s factors through `Fin.cast`. -/
theorem PolyZonotope.mul_point (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p)
    (a : Fin S₁.p → ℝ) :
    (S₁.mul S₂ hp).point a = S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k)) :=
  PolyZonotope.bilin_point Entrywise.hadamardLin S₁ S₂ hp a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
