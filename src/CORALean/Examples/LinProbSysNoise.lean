import CORALean.ContDynamics.LinProbSys.API
import CORALean.ContDynamics.LinearSys.Theorems.NoiseCovarianceDiagonal

/-!
# A linear system with white noise: covariance after a step

The scalar Ornstein-Uhlenbeck process `ẋ = x + ξ` (`A = B = C = 1` in dimension one, `B` unused
by the covariance). A `LinProbSys` is the three matrices, and what it denotes is the Gaussian
law of its solution, so the worked quantity is the covariance of the noise the process picks up
(`noiseCovariance`). It has no float counterpart (a Gaussian process has no machine form), so
nothing runs here; the example is the closed form and the two theorems about it on this instance.

* `noiseCovariance_diagonal` gives `Σ_s(t) = (e^{2t} - 1)/2` at the diagonal `A = 1`.
* `LinProbSys.post_cov` says one `post` step from a state whose probabilistic part has the
  covariance of the noise over time `T = 1`, with input solution the covariance over `Δt = 1`,
  has the covariance over `Δt + T = 2`, that is `(e⁴ - 1)/2`.
* `LinProbSys.initReachCov_lt_noiseCovariance` is the finding on this very instance: CORA's
  `initReach` covariance for `A = C = 1`, `r = 1` is `(1 - e⁻²)/2 ≈ 0.43`, below the true
  `(e² - 1)/2 ≈ 3.19`, so the set built from it is too narrow for an unstable `A`.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.LinProbSysNoise

open CORALean CORALean.Real Matrix

/-- `ẋ = x + u + ξ`. -/
noncomputable def linProbSys : LinProbSys 1 1 where
  A := diagonal fun _ => 1
  B := 1
  C := 1


/-- The noise covariance over time `t`, in closed form. -/
theorem noiseCovariance_closed (t : ℝ) :
    noiseCovariance linProbSys.A linProbSys.C t 0 0 =
      (Real.exp (2 * t) - 1) / 2 := by -- --- PROOF ---
  -- at the diagonal `A = 1` the integral is the closed form
  rw [show linProbSys.A = diagonal fun _ : Fin 1 => (1 : ℝ) from rfl,
    noiseCovariance_diagonal _ _ _ _ _ (by norm_num)]
  simp [linProbSys]
  ring_nf

/-- A state at time `T = 1`: the origin zonotope with the covariance of the noise so far. -/
noncomputable def linProbState : LinProbSys.PostState 1 where
  Rhom := ⟨0, ![0], fun i => i.elim0⟩
  Rpar_det := ⟨![0], ![0]⟩
  Rpar_prob := ⟨⟨0, ![0], fun i => i.elim0⟩, noiseCovariance linProbSys.A linProbSys.C 1⟩
  RauxDet := ⟨0, ![0], fun i => i.elim0⟩

/-- The input solution of one step, `Δt = 1`. -/
noncomputable def linProbInput : ProbZonotope 1 :=
  ⟨⟨0, ![0], fun i => i.elim0⟩, noiseCovariance linProbSys.A linProbSys.C 1⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- After one `post` step both the state and the time-interval set carry the covariance over
time `2`, which is `(e⁴ - 1)/2` by `noiseCovariance_closed`. -/
theorem post_cov_two :
    (linProbSys.post 1 linProbInput linProbState).1.Rpar_prob.cov =
        noiseCovariance linProbSys.A linProbSys.C (1 + 1) ∧
      (linProbSys.post 1 linProbInput linProbState).2.cov =
        noiseCovariance linProbSys.A linProbSys.C (1 + 1) :=
  LinProbSys.post_cov linProbSys 1 1 linProbInput linProbState rfl rfl

/-- Its value, `(e⁴ - 1)/2`. -/
theorem post_cov_value :
    (linProbSys.post 1 linProbInput linProbState).2.cov 0 0 = (Real.exp 4 - 1) / 2 := by
  rw [post_cov_two.2, noiseCovariance_closed]
  norm_num

/-- CORA's input covariance at `A = C = 1`, `r = 1` is below the true noise covariance. -/
example : LinProbSys.initReachCov (fun _ : Fin 1 => (1 : ℝ)) (1 : Mat ℝ 1 1) 1 0 0
    < noiseCovariance (diagonal fun _ : Fin 1 => 1) (1 : Mat ℝ 1 1) 1 0 0 :=
  LinProbSys.initReachCov_lt_noiseCovariance

end CORALean.Examples.LinProbSysNoise


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
