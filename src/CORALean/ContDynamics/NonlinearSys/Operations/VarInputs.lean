import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Real.Operations.Plus
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapMixed

/-!
# `varInputs`, the time-varying part of a polynomialized input

Splitting the abstraction's input at a step into a part fixed at `ts` and a part
varying inside `τs` leaves `v∆(z∆, z, u∆) = B u∆ + ½(D[z, z∆] + D[z∆, z] +
D[z∆, z∆]) + …`, whose set of values is `[1, Eq. 7]`. This is the paper's Sec. 4.2
operator of that name, enclosing it: `B ⊗ U∆`, and half the Minkowski sum of the
three quadratic pairings, `quadMapMixed` twice and `quadMap` once.

Three sets because `[1, Eq. 7]` quantifies over three ranges independently —
`u∆` ranges over `U∆` a second time rather than being read off `z∆`'s input
block — so they are three arguments here rather than one.

Those sums are also why this only encloses: `⊕` lets each term pick its own `z`
and `z∆`, where one member of `[1, Eq. 7]` picks one of each for all three at
once. That costs tightness and nothing else, the caller spending a certificate.

`Real` only: `quadMapMixed` is `bilin` at a `cartProd`, and neither has a float
layer yet, so this waits on a float pairing rather than a rounding decision.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

open Matrix

variable {n m o : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every value the time-varying input part can take over a step, given the
step's three ranges. -/
noncomputable def varInputs (B : Mat ℝ n m) (D : Fin n → Mat ℝ o o)
    (Rz RzΔ : PolyZonotope (Vec ℝ o)) (UΔ : PolyZonotope (Vec ℝ m)) : PolyZonotope (Vec ℝ n) :=
  (PolyZonotope.mtimes B UΔ).plus
    (PolyZonotope.map ((2 : ℝ)⁻¹ • LinearMap.id)
      (((PolyZonotope.quadMapMixed D Rz RzΔ).plus (PolyZonotope.quadMapMixed D RzΔ Rz)).plus
        (PolyZonotope.quadMap D RzΔ)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
