module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point

@[expose] public section

/-!
# The abstraction error of a conservative polynomialization

`IsAbstractionError` at a set, refined so that the error is a *function of the same factors the
initial set is written in* — [1], and what `options.alg = 'poly'` selects in CORA's `linReach`.
The state is `pZ.point a` rather than a member of a set, and the error at that state is
`L.point` at that same `a`, up to `W`. Two pieces, as CORA's `errorStat` and `VerrorDyn` are
two: `L` keeps the dependency and is added back with `exactPlus`, `W` is what had to be boxed.
`L.p = pZ.p` is what "the same factors" means, and `Ba` names a sub-box of the factor domain.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Sonnet 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- At the state factor vector `a` names, the remainder of the affine split is
`L`'s point at that same `a`, widened by `W`. -/
structure IsPolyAbstractionError (f : Vec ℝ n → Vec ℝ m → Vec ℝ n) (A : Mat ℝ n n)
    (B : Mat ℝ n m) (xs : Vec ℝ n) (us : Vec ℝ m) (pZ : Real.PolyZonotope (Vec ℝ n))
    (Ba : Set (Fin pZ.p → ℝ)) (U : Set (Vec ℝ m)) (L : Real.PolyZonotope (Vec ℝ n))
    (hp : L.p = pZ.p) (W : Real.PolyZonotope (Vec ℝ n)) : Prop where
  encloses : ∀ a ∈ Ba, ∀ u ∈ U,
    f (pZ.point a) u - (f xs us + A *ᵥ (pZ.point a - xs) + B *ᵥ (u - us))
      - L.point (fun k => a (Fin.cast hp k)) ∈ W.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
