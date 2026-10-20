module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundSuperlinear
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepCurvatureError
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepRemainderError
public import CORALean.Global.SuperlinearDecrease

@[expose] public section

/-!
# `Thm. 2`: `ε_P` decreases superlinearly

[1, Thm. 2]: `∀φ∈(0,1): ε_P([t_i,t_i+φΔt_i]) ≤ φ·ε_P([t_i,t_i+Δt_i])`, stated
here as `SuperlinearDecrease` at a closed ball around `0` in `ℝ` — the down-set
a nonnegative radius picks out — so `⊆` unfolds to exactly this inequality.
`timePointStepRemainderError`'s own `r` scales linearly and its
`expRemainderBound` factor superlinearly by `Lemma 1`'s own workhorse, so the
proof gets `φ²·ε_P(Δt) ≤ φ·ε_P(Δt)`, tighter than [1]'s own bound.

## Inputs
* `sys` – linear system
* `η` – Taylor order
* `U` – input zonotope
* `Δt` – step length

## Hypotheses
* `hΔt0` – step length positive
* `hΔt` – scaled norm small enough for the Taylor order

## Conclusion
* the remainder error decreases superlinearly in the step

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `timePointStepRemainderError` is nonnegative wherever its side condition
holds and the step is nonnegative. -/
theorem aux_timePointStepRemainderError_nonneg (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 ≤ r)
    (η : ℕ) (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) (U : Zonotope (Vec ℝ n)) :
    (0:ℝ) ≤ sys.timePointStepRemainderError r η U := by -- --- PROOF ---
  have hB : (0:ℝ) ≤ ∑ j, U.absBound j :=
    Finset.sum_nonneg fun j _ => by rw [Zonotope.absBound]; positivity
  have hb0 : (0:ℝ) ≤ MatExp.expRemainderBound (r • toRealMat sys.A) η := by
    have h1 : (0:ℝ) < 1 - ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) := by linarith
    rw [MatExp.expRemainderBound]; positivity
  rw [LinearSys.timePointStepRemainderError]
  positivity


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2]: `ε_P` in eq. (22) decreases superlinearly, at every step
meeting the usual side condition. -/
theorem LinearSys.superlinearDecrease_timePointStepRemainderError (sys : LinearSys 𝕋 n)
    (η : ℕ) (U : Zonotope (Vec ℝ n)) {Δt : ℝ} (hΔt0 : 0 < Δt)
    (hΔt : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) : -- --- CONCL ---
    SuperlinearDecrease
      (fun δ => Metric.closedBall (0:ℝ) (sys.timePointStepRemainderError δ η U))
      Δt := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set B := ∑ j, U.absBound j with hB
  intro φ hφ x hx
  obtain ⟨hφ0, hφ1⟩ := hφ
  have hnonneg : (0:ℝ) ≤ sys.timePointStepRemainderError Δt η U :=
    aux_timePointStepRemainderError_nonneg sys hΔt0.le η hΔt U
  have hbound : MatExp.expRemainderBound ((φ * Δt) • A) η
      ≤ φ * MatExp.expRemainderBound (Δt • A) η := by
    rw [mul_smul]
    exact MatExp.expRemainderBound_superlinear η hφ0 hφ1 hΔt
  have hBnonneg : (0:ℝ) ≤ B := by
    rw [hB]; exact Finset.sum_nonneg fun j _ => by rw [Zonotope.absBound]; positivity
  have h1 : sys.timePointStepRemainderError (φ * Δt) η U
      = 2 * B * ((φ * Δt) * MatExp.expRemainderBound ((φ * Δt) • A) η) := by
    rw [LinearSys.timePointStepRemainderError, ← hA, ← hB]
  have h2 : sys.timePointStepRemainderError Δt η U
      = 2 * B * (Δt * MatExp.expRemainderBound (Δt • A) η) := by
    rw [LinearSys.timePointStepRemainderError, ← hA, ← hB]
  -- `φ²ε_P(Δt) ≤ φε_P(Δt)` since `φ ≤ 1`, tighter than the `φ` [1] itself asks for
  have hkey : sys.timePointStepRemainderError (φ * Δt) η U
      ≤ φ * sys.timePointStepRemainderError Δt η U := by
    have hBφΔ : (0:ℝ) ≤ 2 * B * (φ * Δt) := by positivity
    rw [h2] at hnonneg
    calc sys.timePointStepRemainderError (φ * Δt) η U
        = 2 * B * ((φ * Δt) * MatExp.expRemainderBound ((φ * Δt) • A) η) := h1
      _ ≤ 2 * B * ((φ * Δt) * (φ * MatExp.expRemainderBound (Δt • A) η)) := by gcongr
      _ = φ * φ * (2 * B * (Δt * MatExp.expRemainderBound (Δt • A) η)) := by ring
      _ ≤ φ * 1 * (2 * B * (Δt * MatExp.expRemainderBound (Δt • A) η)) := by gcongr
      _ = φ * sys.timePointStepRemainderError Δt η U := by rw [h2]; ring
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx
  refine Set.mem_smul_set.mpr ⟨x / φ, ?_, ?_⟩
  · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hφ0,
      div_le_iff₀ hφ0]
    calc |x| ≤ sys.timePointStepRemainderError (φ * Δt) η U := hx
      _ ≤ φ * sys.timePointStepRemainderError Δt η U := hkey
      _ = sys.timePointStepRemainderError Δt η U * φ := by ring
  · rw [smul_eq_mul, mul_div_cancel₀ x hφ0.ne']

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
