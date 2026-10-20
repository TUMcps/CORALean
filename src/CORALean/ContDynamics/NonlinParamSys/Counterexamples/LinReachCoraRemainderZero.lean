module

public import CORALean.ContDynamics.NonlinParamSys.NonlinParamSys
public import CORALean.Global.Jacobian
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-!
# The abstraction error of `ẋ = p²` is zero

The Lagrange remainder CORA's `linReach` adds as `Rerror` bounds
`f(x, u, p) - f(x*, u*, p) - ∂f/∂x (x - x*) - ∂f/∂u (u - u*)` through the Hessian in `(x, u)`.
For `ẋ = p²` the field does not depend on `x` or `u`, the Hessian is zero, and the quantity
itself is zero at every `(x, u, p)`: `Rerror = {0}` is exact, so the error set cannot cover the
miss of `linReachCora_misses_counterexample`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the linearization remainder vanishes at every point
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `f(x, u, p) = p²` the linearization remainder vanishes at every point. -/
theorem NonlinParamSys.linReachCora_remainder_zero : -- --- CONCL ---
    let sys : NonlinParamSys 1 1 1 := ⟨fun _ _ p => fun _ => p 0 ^ 2, 1, fun x _ _ => x⟩
    ∀ (xs x : Vec ℝ 1) (us u : Vec ℝ 1) (p : Vec ℝ 1),
      sys.f x u p - (sys.f xs us p + jacobianMat (fun x => sys.f x us p) xs *ᵥ (x - xs)
        + jacobianMat (fun u => sys.f xs u p) us *ᵥ (u - us)) = 0 := by -- --- PROOF ---
  intro sys xs x us u p
  simp [sys, jacobianMat]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
