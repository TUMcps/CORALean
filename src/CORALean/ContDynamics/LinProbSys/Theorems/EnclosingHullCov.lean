module

public import CORALean.ContDynamics.LinProbSys.Operations.EnclosingHull
public import CORALean.ContDynamics.LinProbSys.Theorems.NoiseCovarianceAdd

@[expose] public section

/-!
# The loop of `[1, Alg. 1]` computes the covariance of the hull

After `k` iterations the covariance of `ℛ([kr, (k+1)r])` is `e^{Akr} Σ̂ e^{Aᵀkr} + Σ_s(kr)`, `Σ̂`
that of `ℛ̂([0,r])`: the first interval's noise enters only through the γ-confidence set `η`,
a set of covariance `0`, and each later step adds `Σ_s(r)`, which `noiseCovariance_add` sums to
`Σ_s(kr)`. This presumes `ℛ̲(r)` has the covariance `Σ_s(r)` of `[1, Sec. II]`.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinProbSys.enclosingHull_cov (sys : LinProbSys n m) (r : ℝ) (Rhat : ProbZonotope n)
    (Rbar : Zonotope (Vec ℝ n)) (Runder : ProbZonotope n) (γ : ℝ)
    (hcov : Runder.cov = noiseCovariance sys.A sys.C r) (k : ℕ) : -- --- STMT ---
    (sys.enclosingHull r Rhat Rbar Runder γ k).cov
      = exp (((k : ℝ) * r) • sys.A) * Rhat.cov * (exp (((k : ℝ) * r) • sys.A))ᵀ
        + noiseCovariance sys.A sys.C ((k : ℝ) * r) := by -- --- PROOF ---
  have hT : ∀ s : ℝ, (exp (s • sys.A))ᵀ = exp (s • sys.A.transpose) := fun s => by
    rw [← Matrix.exp_transpose, Matrix.transpose_smul]
  induction k with
  | zero =>
    have h0 : noiseCovariance sys.A sys.C 0 = 0 := by
      funext i j
      simp [noiseCovariance]
    simp [LinProbSys.enclosingHull, ProbZonotope.plus, h0]
  | succ k ih =>
    have hstep : (sys.enclosingHull r Rhat Rbar Runder γ (k + 1)).cov
        = exp (r • sys.A) * (sys.enclosingHull r Rhat Rbar Runder γ k).cov
            * (exp (r • sys.A))ᵀ + noiseCovariance sys.A sys.C r := by
      simp only [LinProbSys.enclosingHull, ProbZonotope.plus, ProbZonotope.mtimes, hcov, zero_add]
    rw [hstep, ih]
    -- the exponentials combine, and the noise sums by `noiseCovariance_add`
    have hz : exp ((((k + 1 : ℕ) : ℝ) * r) • sys.A)
        = exp (r • sys.A) * exp (((k : ℝ) * r) • sys.A) := by
      have hc : Commute (r • sys.A) (((k : ℝ) * r) • sys.A) :=
        ((Commute.refl sys.A).smul_left r).smul_right _
      rw [show (((k + 1 : ℕ) : ℝ) * r) = r + (k : ℝ) * r by push_cast; ring, add_smul]
      exact exp_add_of_commute hc
    have hnoise := noiseCovariance_add sys.A sys.C r ((k : ℝ) * r)
    rw [show r + (k : ℝ) * r = ((k + 1 : ℕ) : ℝ) * r by push_cast; ring, ← hT r] at hnoise
    rw [hnoise, hz, transpose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
