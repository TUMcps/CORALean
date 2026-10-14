module

public import CORALean.HybridDynamics.Theorems.HasDerivAtHitPoint
public import CORALean.HybridDynamics.Theorems.HasDerivAtHitJacobian

@[expose] public section

/-!
# `hitHessian` is the second partial derivative of `hitPoint`

[1, Prop. 2], the second half, as printed: `Q̃⁽ⁱ⁾_lm(x₀) = ∂²y_{h,i}/∂x₀_l∂x₀_m`, the
derivative along the `l`-th axis of the derivative along the `m`-th axis of `y_{h,i}` itself.
Near `x₀` the inner derivative is `L_im` (`hasDerivAt_hitPoint`, wherever `Λ ≠ 0`, which holds
on a neighbourhood since `Λ` is affine), and its derivative along `l` is `Q̃⁽ⁱ⁾_lm`
(`hasDerivAt_hitJacobian`).

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2]: `∂²y_{h,i}/∂x₀_l∂x₀_m = Q̃⁽ⁱ⁾_lm(x₀)`, wherever `Λ(x₀) = nᵀ(Ax₀ + b) ≠ 0`. -/
theorem GuardMap.hasDerivAt_deriv_hitPoint {A : Mat ℝ n n} {b nv x₀ : Vec ℝ n} {d : ℝ}
    (hΛ : nv ⬝ᵥ (A *ᵥ x₀ + b) ≠ 0) (i l m : Fin n) :
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ =>
        GuardMap.hitPoint A b nv d (x₀ + s • Pi.single l 1 + t • Pi.single m 1) i) 0)
      (GuardMap.hitHessian A b nv d x₀ i l m) 0 := by -- --- PROOF ---
  -- `Λ` along the `l`-th axis is continuous, so nonzero near `s = 0`
  have hcont : Continuous fun s : ℝ => nv ⬝ᵥ (A *ᵥ (x₀ + s • Pi.single l 1) + b) := by
    have hform : (fun s : ℝ => nv ⬝ᵥ (A *ᵥ (x₀ + s • Pi.single l 1) + b))
        = fun s => nv ⬝ᵥ (A *ᵥ x₀ + b) + s * (nv ᵥ* A) l := by
      funext s
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
        Matrix.mulVec_single_one, smul_eq_mul]
      rw [show nv ⬝ᵥ col A l = (nv ᵥ* A) l from rfl]
      ring
    rw [hform]
    fun_prop
  have hev : ∀ᶠ s in nhds (0 : ℝ), nv ⬝ᵥ (A *ᵥ (x₀ + s • Pi.single l 1) + b) ≠ 0 :=
    hcont.continuousAt.eventually_ne (by simpa using hΛ)
  refine (GuardMap.hasDerivAt_hitJacobian hΛ i l m).congr_of_eventuallyEq ?_
  filter_upwards [hev] with s hs
  exact (GuardMap.hasDerivAt_hitPoint hs i m).deriv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
