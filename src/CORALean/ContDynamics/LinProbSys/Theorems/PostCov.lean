module

public import CORALean.ContDynamics.LinProbSys.Operations.Post
public import CORALean.ContDynamics.LinProbSys.Theorems.NoiseCovarianceAdd

@[expose] public section

/-!
# The covariance of `post` is the noise covariance one step later

If the probabilistic particular solution `Rpar_prob` has the covariance `Σ_s(T)` of the noise
accumulated over `T`, and the input solution of one step `pRinput` that of `Δt`, then the one
`post` returns, and the one of the time-interval set `Rnext.ti`, is `Σ_s(Δt + T)`: the
recursion `eAt Σ eAtᵀ + Σ₁` is exact. Only the covariance: the sets `Rhom`, `Rpar_det`,
`RauxDet` and the means have no statement here. CORA's `initReach` puts a wrong `pRinput` in
(`references/coverage/contDynamics/linProbSys.md`, row `initReach`); `LinProbSys.initReach`, sign
corrected, meets both hypotheses (`initReach_cov`). The recursion is that of [1, Sec. II].

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

open CORALean.Real Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinProbSys.post_cov (sys : LinProbSys n m) (Δt T : ℝ) (pRinput : ProbZonotope n)
    (st : LinProbSys.PostState n) (hst : st.Rpar_prob.cov = noiseCovariance sys.A sys.C T)
    (hp : pRinput.cov = noiseCovariance sys.A sys.C Δt) :
    (sys.post Δt pRinput st).1.Rpar_prob.cov = noiseCovariance sys.A sys.C (Δt + T) ∧
      (sys.post Δt pRinput st).2.cov = noiseCovariance sys.A sys.C (Δt + T) := by -- --- PROOF ---
  -- the covariance is `e^{AΔt} Σ(T) e^{(AΔt)ᵀ} + Σ(Δt)`, `noiseCovariance_add`
  have hadd := noiseCovariance_add sys.A sys.C Δt T
  have hT : (exp (Δt • sys.A))ᵀ = exp (Δt • sys.A.transpose) := by
    rw [← Matrix.exp_transpose, Matrix.transpose_smul]
  simp only [LinProbSys.post, ProbZonotope.plus, ProbZonotope.mtimes, hst, hp, hT]
  refine ⟨hadd.symm, ?_⟩
  rw [zero_add, add_zero]
  exact hadd.symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
