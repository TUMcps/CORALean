import CORALean.ContDynamics.LinProbSys.Operations.ReachCovCora
import CORALean.ContDynamics.LinProbSys.Theorems.InitReachCovLt
import CORALean.ContDynamics.LinProbSys.Theorems.NoiseCovarianceAdd

/-!
# CORA's reach loop keeps the too-small covariance for an unstable `A`

In `ℝ¹` with `A = C = 1` and `r = 1`, after any `k ≥ 1` steps the covariance CORA's `reach`
carries (`reachCovCora`, [1]) is strictly below the noise covariance `Σ_s(k r)` of the process:
`post` multiplies the covariance by `e²` and adds `pRinput`'s, and `pRinput`'s is already
below the true one (`initReachCov_lt_noiseCovariance`), so the gap persists and grows.

## References

* [1] `contDynamics/@contDynamics/reach.m`, `contDynamics/@linProbSys/initReach.m`,
      `private/priv_inputSolution.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinProbSys.reachCovCora_lt_counterexample (B : Mat ℝ 1 1)
    (st0 : LinProbSys.PostState 1) (h0 : st0.Rpar_prob.cov = 0) (k : ℕ) (hk : 1 ≤ k) :
    (⟨diagonal fun _ => 1, B, 1⟩ : LinProbSys 1 1).reachCovCora (fun _ => 1) 1 st0 k 0 0
      < noiseCovariance (diagonal fun _ : Fin 1 => (1 : ℝ)) (1 : Mat ℝ 1 1) (k * 1) 0 0
    := by -- --- PROOF ---
  set sys : LinProbSys 1 1 := ⟨diagonal fun _ => 1, B, 1⟩ with hsys
  rw [mul_one]
  have hlt : LinProbSys.initReachCov (fun _ : Fin 1 => (1 : ℝ)) (1 : Mat ℝ 1 1) 1 0 0
      < noiseCovariance sys.A sys.C 1 0 0 := LinProbSys.initReachCov_lt_noiseCovariance
  have hexp : exp ((1 : ℝ) • sys.A) = diagonal fun _ : Fin 1 => Real.exp 1 := by
    rw [show sys.A = diagonal fun _ : Fin 1 => (1 : ℝ) from rfl, ← diagonal_smul,
      Matrix.exp_diagonal]
    simp [Real.exp_eq_exp_ℝ]
  have hEt : (exp ((1 : ℝ) • sys.A))ᵀ = exp ((1 : ℝ) • sys.A) := by
    rw [hexp, diagonal_transpose]
  have hAt : sys.Aᵀ = sys.A := by
    rw [show sys.A = diagonal fun _ : Fin 1 => (1 : ℝ) from rfl, diagonal_transpose]
  have hdiag : ∀ M : Mat ℝ 1 1, (exp ((1 : ℝ) • sys.A) * M * exp ((1 : ℝ) • sys.A)) 0 0
      = Real.exp 1 * M 0 0 * Real.exp 1 := by
    intro M
    rw [hexp]
    simp [Matrix.mul_apply]
  -- the true covariance obeys `t (k+1) = e² t k + σ`
  have htrue : ∀ k : ℕ, noiseCovariance sys.A sys.C ((k : ℝ) + 1) 0 0
      = Real.exp 1 * noiseCovariance sys.A sys.C (k : ℝ) 0 0 * Real.exp 1
        + noiseCovariance sys.A sys.C 1 0 0 := by
    intro k
    have := congrFun (congrFun (noiseCovariance_add sys.A sys.C 1 (k : ℝ)) 0) 0
    rw [add_comm, this, Matrix.add_apply, hAt, hdiag]
  have hc : ∀ k : ℕ, sys.reachCovCora (fun _ => 1) 1 st0 (k + 1) 0 0
      = Real.exp 1 * sys.reachCovCora (fun _ => 1) 1 st0 k 0 0 * Real.exp 1
        + LinProbSys.initReachCov (fun _ : Fin 1 => (1 : ℝ)) (1 : Mat ℝ 1 1) 1 0 0 := by
    intro k
    simp only [LinProbSys.reachCovCora, Function.iterate_succ_apply', LinProbSys.post,
      ProbZonotope.plus, ProbZonotope.mtimes]
    rw [hEt, Matrix.add_apply, hdiag]
  have h00 : sys.reachCovCora (fun _ => 1) 1 st0 0 = 0 := by
    simpa [LinProbSys.reachCovCora] using h0
  have hT0 : noiseCovariance sys.A sys.C 0 0 0 = 0 := by
    simp [noiseCovariance]
  -- induction: `≤` always, hence `<` after one step
  have hle : ∀ k : ℕ, sys.reachCovCora (fun _ => 1) 1 st0 k 0 0
      ≤ noiseCovariance sys.A sys.C (k : ℝ) 0 0 := by
    intro k
    induction k with
    | zero => rw [h00]; simp [hT0]
    | succ k ih =>
      rw [hc, Nat.cast_succ, htrue]
      have := Real.exp_pos 1
      nlinarith [mul_le_mul_of_nonneg_right ih this.le, mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ih this.le) this.le]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [hc, Nat.cast_succ, htrue]
  have := Real.exp_pos 1
  nlinarith [mul_le_mul_of_nonneg_right (hle j) this.le, mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hle j) this.le) this.le]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
