module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExponentialRemainder
public import CORALean.ContSet.VPolytope.Real.Operations.Basic
public import CORALean.ContSet.VPolytope.Real.Operations.Plus
public import CORALean.ContSet.VPolytope.Real.Operations.Point
public import CORALean.ContSet.VPolytope.Real.Operations.Map
public import CORALean.ContSet.Conversion.Real.Operations.VPolytope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# `MatExp.expmIndPolytope`

CORA's `@matPolytope/expmInd(matP, maxOrder)`, which `@matPolytope/expm(matP, maxOrder)` calls with
the default `maxOrder = 10`: the Taylor sum of the matrix polytope, `Σ_{i ≤ maxOrder} matP^i / i!`
by Minkowski sums of vertex products, and the vertices of the remainder box `exponentialRemainder`
of its interval matrix added to it. CORA's `matP^i` here is the running product `ePpow * matP`,
started from the identity. The Minkowski sums are `VPolytope.plus`, which keeps all vertex sums
where CORA keeps the hull vertices.

## Inputs
* `P` – matrix polytope
* `η` – Taylor order

## Output
* matrix polytope enclosing the exponential of every member
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `eP = expmInd(matP, maxOrder)`: a matrix polytope enclosing `e^M` for every member `M`. -/
noncomputable def MatExp.expmIndPolytope (P : VPolytope (Mat ℝ n n)) (η : ℕ) :
    VPolytope (Mat ℝ n n) :=
  -- 1. `ePpow = matP^0`, then `ePpow = ePpow * matP`; `ePpow i` is the value after `i` passes
  let ePpow := fun i : ℕ => (fun Q => VPolytope.matMul Q P)^[i] (VPolytope.point 1)
  -- 2. `eP = matP^0`, then `eP = eP + ePpow * (1 / i!)` for `i = 1 … maxOrder`
  let eP := (List.range' 1 η).foldl (fun e i => VPolytope.plus e
    ((ePpow i).map ((Nat.factorial i : ℝ)⁻¹ • LinearMap.id))) (VPolytope.point 1)
  -- 3. `E = exponentialRemainder(intervalMatrix(matP), maxOrder)` and `eP = eP + matPolytope(E)`
  VPolytope.plus eP (Interval.matPolytope (MatExp.exponentialRemainder P.intervalMatrix η))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
