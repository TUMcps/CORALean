import CORALean.ContSet.SpectraShadow.Real.Operations.ArrowMat

/-!
# The quadratic form of the arrowhead matrix

For `x = (a, y)` the quadratic form of `arrowMat s t w` is `t a² + 2 a ⟨w, y⟩ + s ‖y‖²`, which
completes to `‖s y + a w‖² + a² (s t - ‖w‖²)` over `s` when `s > 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem arrowMat_quadForm (s t : ℝ) (w : Vec ℝ N) (x : Vec ℝ (N + 1)) :
    x ⬝ᵥ arrowMat s t w *ᵥ x
      = t * x 0 ^ 2 + 2 * x 0 * (w ⬝ᵥ fun i : Fin N => x i.succ)
        + s * ((fun i : Fin N => x i.succ) ⬝ᵥ fun i : Fin N => x i.succ) := by -- --- PROOF ---
  -- expand the double sum over the first coordinate and the rest
  simp only [dotProduct, mulVec, Fin.sum_univ_succ, arrowMat, Matrix.of_apply, Fin.cases_zero,
    Fin.cases_succ, mul_add, Finset.mul_sum, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_add_distrib]
  -- the two cross terms are one
  have h1 : ∑ i : Fin N, x i.succ * (w i * x 0) + ∑ i : Fin N, x 0 * (w i * x i.succ)
      = ∑ i : Fin N, 2 * x 0 * (w i * x i.succ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i : Fin N, x i.succ * (s * x i.succ) = ∑ i : Fin N, s * (x i.succ * x i.succ) :=
    Finset.sum_congr rfl fun i _ => by ring
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
