import CORALean.Global.TaylorLagrangeConvex
import Mathlib.Analysis.Convex.Segment

/-!
# The first-order expansion with its Lagrange remainder on the segment

[1, Eq. 2]: the first-order Taylor expansion of `fᵢ` at the linearization point `z*`, with the
Lagrange remainder `½ (z - z*)ᵀ ∂²fᵢ(ξ)/∂z² (z - z*)` at some `ξ` on the segment from `z*` to
`z`, is `fᵢ(z)` exactly. The Hessian's quadratic form is the second Fréchet derivative applied
to `z - z*` in both slots; `taylor_lagrange_convex` at order one on the segment, which is
convex and holds both ends, gives the point.

The paper's `z` is the state and the input, and its parameter `p` enters `fᵢ` beside them; here
`fᵢ` is any `C²` function of the stacked variable, which a parameter is one more coordinate of.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 2]: `f(z) = f(z*) + ∇f(z*)(z - z*) + ½ (z - z*)ᵀ ∇²f(ξ) (z - z*)` for some `ξ` on
the segment from `z*` to `z`. -/
theorem taylor_lagrange_segment {f : Vec ℝ n → ℝ} (hf : ContDiff ℝ 2 f) (zs z : Vec ℝ n) :
    ∃ ξ ∈ segment ℝ zs z, f z = f zs + fderiv ℝ f zs (z - zs)
      + iteratedFDeriv ℝ 2 f ξ (fun _ => z - zs) / 2 := by -- --- PROOF ---
  obtain ⟨ξ, hξ, h⟩ := taylor_lagrange_convex (N := 1) hf (convex_segment zs z)
    (left_mem_segment ℝ zs z) (right_mem_segment ℝ zs z)
  refine ⟨ξ, hξ, ?_⟩
  -- the order-`0` and order-`1` terms are the value and the derivative
  rw [h, Finset.sum_range_succ, Finset.sum_range_one, iteratedFDeriv_zero_apply,
    iteratedFDeriv_one_apply]
  norm_num

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
