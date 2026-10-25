module

public import CORALean.ContDynamics.LinearSys.Definitions.NoiseCovariance
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

/-!
# The noise covariance is positive semidefinite

`Σ_s(t) = ∫₀ᵗ e^{A(t-τ)} C Cᵀ e^{Aᵀ(t-τ)} dτ` for `t ≥ 0`, the covariance matrix of a Gaussian
`[1, Sec. II]`: symmetric, since the integrand `(e^{uA} C)(e^{uA} C)ᵀ` is, and `xᵀ Σ_s(t) x` is
the integral of `‖(e^{uA} C)ᵀ x‖²`. It is what lets Gaussians with this covariance be added and
mapped as laws, as `[1, Prop. 4]` does.

## Inputs
* `A` – system matrix
* `C` – noise matrix
* `t` – time

## Hypotheses
* `ht` – time nonnegative

## Conclusion
* the noise covariance is positive semidefinite

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem noiseCovariance_posSemidef (A : Mat ℝ n n) (C : Mat ℝ n m) {t : ℝ}
    (ht : 0 ≤ t) : -- --- CONCL ---
    (noiseCovariance A C t).PosSemidef := by -- --- PROOF ---
  set g : ℝ → Mat ℝ n n := fun u => exp (u • A) * (C * C.transpose) * exp (u • A.transpose)
    with hg
  have hcont : ∀ k l, Continuous fun u => g u k l := fun k l => by
    have h1 : Continuous fun u : ℝ => exp (u • A) := exp_continuous.comp (continuous_id.smul
      continuous_const)
    have h2 : Continuous fun u : ℝ => exp (u • A.transpose) :=
      exp_continuous.comp (continuous_id.smul continuous_const)
    exact (((h1.mul continuous_const).mul h2).matrix_elem k l)
  -- the covariance over `u = t - τ`
  have hcov : ∀ k l, noiseCovariance A C t k l = ∫ u in (0 : ℝ)..t, g u k l := by
    intro k l
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t)
      (fun u => g u k l) t
    simpa [noiseCovariance, hg] using h
  -- the integrand is symmetric and `xᵀ g(u) x = ‖(e^{uA} C)ᵀ x‖²` is nonnegative
  have hgT : ∀ u, (g u).transpose = g u := fun u => by
    simp only [hg, transpose_mul, Matrix.mul_assoc, transpose_transpose, ← Matrix.exp_transpose,
      transpose_smul]
  have hgpsd : ∀ u, (g u).PosSemidef := fun u => by
    have := (Matrix.posSemidef_self_mul_conjTranspose (exp (u • A) * C))
    convert this using 1
    simp only [hg, conjTranspose_eq_transpose_of_trivial, transpose_mul, ← Matrix.exp_transpose,
      transpose_smul, Matrix.mul_assoc]
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext k l
    simp only [conjTranspose_apply, star_trivial, hcov]
    exact intervalIntegral.integral_congr fun u _ => by
      simpa using (congrFun (congrFun (hgT u) k) l)
  · -- the quadratic form is the integral of the integrand's
    have hint : ∀ k l, IntervalIntegrable (fun u => x k * (g u k l * x l))
        MeasureTheory.volume 0 t := fun k l =>
      (continuous_const.mul ((hcont k l).mul continuous_const)).intervalIntegrable _ _
    have hq : x ⬝ᵥ noiseCovariance A C t *ᵥ x
        = ∫ u in (0 : ℝ)..t, x ⬝ᵥ g u *ᵥ x := by
      simp only [dotProduct, mulVec, hcov, Finset.mul_sum]
      rw [intervalIntegral.integral_finsetSum (f := fun k u => ∑ l, x k * (g u k l * x l))
        fun k _ => (continuous_finsetSum _ fun l _ => continuous_const.mul
          ((hcont k l).mul continuous_const)).intervalIntegrable _ _]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_finsetSum (f := fun l u => x k * (g u k l * x l))
        fun l _ => hint k l]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
    rw [star_trivial, hq]
    exact intervalIntegral.integral_nonneg ht fun u _ => by
      simpa using (hgpsd u).dotProduct_mulVec_nonneg x

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
