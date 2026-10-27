module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Map
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.PolyZonotope.Real.Operations.Plus
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapMixed

@[expose] public section

/-!
# `varInputs`, the time-varying part of a polynomialized input

Splitting the abstraction's input at a step into a part fixed at `ts` and a part varying inside
`τs` leaves `v∆(z∆, z, u∆) = B u∆ + ½(D[z, z∆] + D[z∆, z] + D[z∆, z∆]) + …`, whose set of values
is `[1, Eq. 7]`. This is the paper's Sec. 4.2 operator of that name, enclosing it: `B ⊗ U∆`, and
half the Minkowski sum of the three quadratic pairings. Three sets, since `[1, Eq. 7]` quantifies
over three ranges independently. It only encloses: `⊕` lets each term pick its own `z` and `z∆`,
which costs tightness and nothing else. `Real` only: `quadMapMixed` has no float layer yet.

## Inputs
* `B` – input matrix
* `D` – Hessian family
* `Rz` – state-input range
* `RzΔ` – varying state-input range
* `UΔ` – varying input range

## Output
* the polynomial zonotope enclosing the varying input part

## References

* [1] [M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative Polynomialization
      and Non-Convex Sets". Proceedings of the 16th international conference on Hybrid systems:
      computation and control,
      2013.](../../../../../references/2013/althoff-hscc-conservative-polynomialization.md)
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
