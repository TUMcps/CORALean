module

public import CORALean.ContDynamics.LinearSys.Definitions.InputLawsOver
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.NoiseCovariancePosSemidef
public import CORALean.ContDynamics.LinProbSys.Theorems.NoiseCovarianceAdd

@[expose] public section

/-!
# With the origin an input, the interval's laws are dominated by the one at its end

`[1, Prop. 4]`, proof: "the reachable set `η(R̄([0,r]), γ)` is growing from the origin, such that
the reachable set for `t ∈ [0, r]` equals the reachable set at `t = r`". With `0 ∈ U` every law
over `[0, r]` has its mean among the input solution's at `r` (`LinearSys.inputReach_mono`) and its
covariance `Σ_s(t)` below `Σ_s(r)` in the Loewner order: `Σ_s(r) - Σ_s(t) = e^{At} Σ_s(r-t) e^{Aᵀt}`
(`noiseCovariance_add`) is positive semidefinite. So `R̄(r)` represents the whole interval, in
the means and in the covariance.

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

open Matrix ContSet Scalar NormedSpace MeasureTheory ProbabilityTheory WithLp

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
  [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in
theorem LinearSys.inputLawsOver_dominated (sys : LinearSys 𝕋 n) (C : Mat ℝ n m) {U : S n}
    {r : ℝ} (hbdd : Bornology.IsBounded (construct U))
    (h0 : (0 : Vec ℝ n) ∈ construct U) : -- --- CONCL ---
    ∀ ν ∈ sys.inputLawsOver C U 0 r, ∃ y ∈ sys.inputReach U r, ∃ t ∈ Set.Icc (0 : ℝ) r,
      ν = multivariateGaussian (toLp 2 y) (noiseCovariance (toRealMat sys.A) C t) ∧
        (noiseCovariance (toRealMat sys.A) C r - noiseCovariance (toRealMat sys.A) C t).PosSemidef
        := by -- --- PROOF ---
  rintro ν ⟨t, ⟨ht0, htr⟩, y, hy, rfl⟩
  refine ⟨y, sys.inputReach_mono hbdd h0 ht0 htr hy, t, ⟨ht0, htr⟩, rfl, ?_⟩
  set A := toRealMat sys.A with hA
  -- `Σ_s(r) = e^{At} Σ_s(r - t) e^{Aᵀt} + Σ_s(t)`
  have hadd := noiseCovariance_add A C t (r - t)
  rw [show t + (r - t) = r by ring] at hadd
  have hT : (exp (t • A))ᵀ = exp (t • A.transpose) := by
    rw [← Matrix.exp_transpose, Matrix.transpose_smul]
  rw [hadd, add_sub_cancel_right, ← hT]
  simpa [Matrix.mul_assoc] using
    (noiseCovariance_posSemidef A C (by linarith : 0 ≤ r - t)).mul_mul_conjTranspose_same
      (exp (t • A))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
