module

public import CORALean.ContDynamics.NonlinParamSys.Theorems.JacobianFamilyMem

@[expose] public section

/-!
# `zB` holds the input Jacobian at every parameter of the box

For a system affine in `p` and differentiable in the input, `∂f/∂u (x*, u*, p)` lies in the matrix
zonotope `zB` of `linearize` for every `p` of the parameter box (`jacobianFamily_mem` at the input).
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

theorem NonlinParamSys.linearize_jacobianU_mem (sys : NonlinParamSys n m q)
    (hAff : ∀ x u p, sys.f x u p
      = sys.f x u 0 + ∑ i, p i • (sys.f x u (Pi.single i 1) - sys.f x u 0))
    (xs : Vec ℝ n) (us : Vec ℝ m)
    (hd : ∀ p, DifferentiableAt ℝ (fun u => sys.f xs u p) us) (I : Interval (Vec ℝ q))
    {p : Vec ℝ q} (hp : p ∈ I.construct) :
    jacobianMat (fun u => sys.f xs u p) us ∈ (sys.linearize xs us I).1.B.construct :=
  NonlinParamSys.jacobianFamily_mem (fun u p => sys.f xs u p) (fun u p => hAff xs u p) us hd I hp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
