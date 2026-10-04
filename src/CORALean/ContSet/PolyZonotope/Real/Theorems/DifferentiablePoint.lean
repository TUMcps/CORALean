import CORALean.ContSet.PolyZonotope.Real.Operations.Point
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The point map is differentiable

`a ↦ c + ∑ᵢ (∏ₖ aₖ^{Eₖᵢ}) · Gᵢ` is a polynomial in the factors, so differentiable in the sup norm
of `Fin p → ℝ`: each monomial is a finite product of powers of coordinates.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.differentiable_point (pZ : PolyZonotope (Vec ℝ n)) :
    Differentiable ℝ pZ.point := by -- --- PROOF ---
  have hm : ∀ i, Differentiable ℝ (fun a : Fin pZ.p → ℝ => PolyZonotope.monomial pZ.E a i) := by
    intro i a
    unfold PolyZonotope.monomial
    classical
    have hg : ∀ k ∈ (Finset.univ : Finset (Fin pZ.p)),
        DifferentiableAt ℝ (fun a : Fin pZ.p → ℝ => a k ^ pZ.E k i) a :=
      fun k _ => ((differentiable_apply k).fun_pow _) a
    exact (HasFDerivAt.finsetProd (fun k hk => (hg k hk).hasFDerivAt)).differentiableAt
  unfold PolyZonotope.point
  exact (differentiable_const _).add (Differentiable.fun_sum fun i _ => (hm i).smul_const _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
