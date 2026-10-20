module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes
public import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapMixed
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `varInputs`, the time-varying part of a polynomialized input, in floats

Splitting the abstraction's input at a step into a part fixed at `ts` and a part varying inside
`τs` leaves `v∆(z∆, z, u∆) = B u∆ + ½(D[z, z∆] + D[z∆, z] + D[z∆, z∆]) + …`, whose set of values
is `[1, Eq. 7]`. This is `varInputs` over `Float.PolyZonotope`, one named `let` per printed
term: `B ⊗ U∆`, and half the sum of the three quadratic pairings, `quadMapMixed` twice and
`quadMap` once. The halving is `mtimes` by `½ I`, which is exact in a binary format and so costs
the error box nothing it does not already carry.

## Inputs
* `B` – input matrix
* `D` – Hessian family
* `Rz` – state-input range
* `RzΔ` – varying state-input range
* `UΔ` – varying input range

## Output
* the float polynomial zonotope enclosing the varying input part

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m o : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `½ I`, the scaling of the second-order part. -/
def aux_halfMat (n : ℕ) : Mat 𝕋 n n := fun i j => if i = j then half one else zero


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every value the time-varying input part can take over a step, given the step's three ranges,
enclosed. -/
def varInputsFloat (B : Mat 𝕋 n m) (D : Fin n → Mat 𝕋 o o)
    (Rz RzΔ : PolyZonotope (Vec 𝕋 o)) (UΔ : PolyZonotope (Vec 𝕋 m)) : PolyZonotope (Vec 𝕋 n) :=
  let BU := PolyZonotope.mtimes B UΔ                       -- B ⊗ U∆
  let DzzΔ := PolyZonotope.quadMapMixed D Rz RzΔ           -- D[z, z∆]
  let DzΔz := PolyZonotope.quadMapMixed D RzΔ Rz           -- D[z∆, z]
  let DzΔzΔ := PolyZonotope.quadMap D RzΔ                  -- D[z∆, z∆]
  let quad := (DzzΔ.plus DzΔz).plus DzΔzΔ                  -- the three pairings
  BU.plus (PolyZonotope.mtimes (aux_halfMat n) quad)           -- B U∆ + ½ (…)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
