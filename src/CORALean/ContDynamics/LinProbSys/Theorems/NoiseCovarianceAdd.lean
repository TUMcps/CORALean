module

public import CORALean.ContDynamics.LinearSys.Definitions.NoiseCovariance
public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeReachSetExactSubsetInputReach

@[expose] public section

/-!
# The noise covariance over two steps

`Σ_s(s + t) = e^{As} Σ_s(t) e^{Aᵀs} + Σ_s(s)`: the noise of a time `t` carried through `s`, plus
the noise picked up in `s`. The identity behind `post`'s recursion `eAt Σ eAtᵀ + Σ₁` for the
covariance of the particular solution [1, Sec. II]. Entry by entry, as `noiseCovariance` is.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The integrand over `u = t - τ`, a continuous matrix function. -/
theorem aux_noiseIntegrand_continuous (A : Mat ℝ n n) (C : Mat ℝ n m) (i j : Fin n) :
    Continuous fun u : ℝ =>
      (exp (u • A) * (C * C.transpose) * exp (u • A.transpose)) i j := by -- --- PROOF ---
  -- each factor is continuous in `u`, and an entry of a product is a finite sum of products
  have h1 : Continuous fun u : ℝ => exp (u • A) := exp_continuous.comp (continuous_id.smul
    continuous_const)
  have h2 : Continuous fun u : ℝ => exp (u • A.transpose) :=
    exp_continuous.comp (continuous_id.smul continuous_const)
  exact (((h1.mul continuous_const).mul h2).matrix_elem i j)


-- =======================================  MAIN THEOREM  ======================================= --

theorem noiseCovariance_add (A : Mat ℝ n n) (C : Mat ℝ n m) (s t : ℝ) :
    noiseCovariance A C (s + t)
      = exp (s • A) * noiseCovariance A C t * exp (s • A.transpose)
        + noiseCovariance A C s := by -- --- PROOF ---
  set g : ℝ → Mat ℝ n n := fun u => exp (u • A) * (C * C.transpose) * exp (u • A.transpose)
    with hg
  have hcont : ∀ k l, Continuous fun u => g u k l := fun k l =>
    aux_noiseIntegrand_continuous A C k l
  have hint : ∀ k l a b, IntervalIntegrable (fun u => g u k l) MeasureTheory.volume a b :=
    fun k l a b => (hcont k l).intervalIntegrable a b
  -- the covariance over `u = T - τ`
  have hcov : ∀ T k l, noiseCovariance A C T k l = ∫ u in (0 : ℝ)..T, g u k l := by
    intro T k l
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := T)
      (fun u => g u k l) T
    simpa [noiseCovariance, hg] using h
  -- the exponentials shift: `g (s + v) = e^{As} g(v) e^{Aᵀs}`
  have hshift : ∀ v, g (s + v) = exp (s • A) * g v * exp (s • A.transpose) := by
    intro v
    have hA : exp ((s + v) • A) = exp (s • A) * exp (v • A) := by
      have hc : Commute (s • A) (v • A) := ((Commute.refl A).smul_left s).smul_right v
      rw [add_smul]
      exact exp_add_of_commute hc
    have hB : exp ((s + v) • A.transpose) = exp (v • A.transpose) * exp (s • A.transpose) := by
      have hc : Commute (v • A.transpose) (s • A.transpose) :=
        ((Commute.refl A.transpose).smul_left v).smul_right s
      rw [add_comm, add_smul]
      exact exp_add_of_commute hc
    simp only [hg, hA, hB, Matrix.mul_assoc]
  funext i j
  simp only [Matrix.add_apply]
  -- the integral over `[0, s + t]` splits at `s`
  rw [hcov, hcov, ← intervalIntegral.integral_add_adjacent_intervals (hint i j 0 s)
    (hint i j s (s + t)), add_comm]
  congr 1
  -- the part past `s` is the shifted integral of `g`
  have hsh := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := t)
    (fun u => g u i j) s
  rw [add_zero] at hsh
  rw [← hsh]
  -- an entry of `E Σ(t) E'` is a double sum, and the integral passes through it
  have hexp : ∀ v, (exp (s • A) * g v * exp (s • A.transpose)) i j
      = ∑ k, ∑ l, exp (s • A) i l * g v l k * exp (s • A.transpose) k j := by
    intro v
    simp only [Matrix.mul_apply, Finset.sum_mul]
  simp only [hshift, hexp, Matrix.mul_apply, hcov, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum fun k _ => (continuous_finsetSum _ fun l _ =>
    ((hcont l k).const_mul _).mul_const _).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_finsetSum fun l _ =>
    (((hcont l k).const_mul _).mul_const _).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
