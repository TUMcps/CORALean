module

public import CORALean.ContDynamics.NonlinParamSys.Theorems.JacobianFamilyMem

@[expose] public section

/-!
# `zA` holds the state Jacobian at every parameter of the box

For a system affine in `p` and differentiable in the state, `∂f/∂x (x*, u*, p)` lies in the matrix
zonotope `zA` of `linearize` for every `p` of the parameter box (`jacobianFamily_mem` at the state).

## Inputs
* `sys` – parametric system
* `xs` – state expansion point
* `us` – input expansion point
* `I` – parameter box
* `p` – parameter vector

## Hypotheses
* `hAff` – the dynamics are affine in the parameter
* `hd` – differentiable in the state
* `hp` – `p` lies in the box

## Conclusion
* the state Jacobian at the parameter lies in `zA`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.linearize_jacobianX_mem (sys : NonlinParamSys n m q)
    (hAff : ∀ x u p, sys.f x u p
      = sys.f x u 0 + ∑ i, p i • (sys.f x u (Pi.single i 1) - sys.f x u 0))
    (xs : Vec ℝ n) (us : Vec ℝ m)
    (hd : ∀ p, DifferentiableAt ℝ (fun x => sys.f x us p) xs) (I : Interval (Vec ℝ q))
    {p : Vec ℝ q} (hp : p ∈ I.construct) :
    jacobianMat (fun x => sys.f x us p) xs ∈ (sys.linearize xs us I).1.A.construct :=
  NonlinParamSys.jacobianFamily_mem (fun x p => sys.f x us p) (fun x p => hAff x us p) xs hd I hp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
