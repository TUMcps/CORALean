module

public import CORALean.ContDynamics.LinearSys.Operations.StepInputConst
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.StepInputEqShifted

@[expose] public section

/-!
# A constant input steps exactly by `stepInputConst`

`hu` is assumed only on `[k·Δt, (k+1)·Δt]`, the interval a zero-order hold actually pins `u` to; the
whole-line hypothesis of #43's sketch would have been an unnecessary restriction on a caller.
`hΔt : 0 ≤ Δt` is needed beyond what that sketch names: `expIntegral_mulVec` only reads the series
as the integral at a non-negative endpoint, and `stepInputConst` carries no sign restriction of its
own. The route: `stepInput_eq_shifted` moves the step to `[0, Δt]`, `hu` collapses the shifted input
to `c` there, and `expIntegral_mulVec` read against `intervalIntegral.integral_comp_sub_left` turns
the propagated integral back into `expIntegral · Δt` applied to `c`.

## Inputs
* `sys` – linear system
* `c` – constant vector
* `Δt` – step length
* `u` – input signal
* `k` – step index

## Hypotheses
* `hΔt` – step length nonnegative
* `hu` – input equals the constant on the step

## Conclusion
* the step input is the integrated exponential applied to the constant
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `stepInputConst`, read back as the propagator integrated against `c` on the
step's own clock: `expIntegral_mulVec` composed with the substitution that
turns `Δt - σ` back into `σ`. -/
private theorem aux_stepInputConst_eq_shifted (sys : LinearSys 𝕋 n) (c : Vec ℝ n) {Δt : ℝ}
    (hΔt : 0 ≤ Δt) :
    sys.stepInputConst c Δt
      = ∫ σ in (0:ℝ)..Δt, exp ((Δt - σ) • toRealMat sys.A) *ᵥ c := by
  rw [LinearSys.stepInputConst, Real.MatExp.expIntegral_mulVec (toRealMat sys.A) c hΔt]
  have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := Δt)
    (fun σ : ℝ => exp (σ • toRealMat sys.A) *ᵥ c) Δt
  simpa using h.symm


-- =======================================  MAIN THEOREM  ======================================= --

/-- A `u` pinned to `c` on step `k`'s own interval steps exactly by
`stepInputConst c Δt`: the exponential integral applied to that one vector
rather than to every point of a set, at every instant of the step. -/
theorem LinearSys.stepInput_const (sys : LinearSys 𝕋 n) (c : Vec ℝ n) {Δt : ℝ}
    (hΔt : 0 ≤ Δt) (u : ℝ → Vec ℝ n) (k : ℕ)
    (hu : ∀ s ∈ Set.Icc ((k:ℝ) * Δt) (((k:ℝ) + 1) * Δt), u s = c) : -- --- CONCL ---
    sys.stepInput u Δt k = sys.stepInputConst c Δt := by -- --- PROOF ---
  rw [sys.stepInput_eq_shifted, aux_stepInputConst_eq_shifted sys c hΔt]
  -- the shifted input collapses to `c` on the step, so the integrands agree
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [Set.uIcc_of_le hΔt] at hσ
  have hexpand : ((k:ℝ) + 1) * Δt = (k:ℝ) * Δt + Δt := by ring
  have hmem : (k:ℝ) * Δt + σ ∈ Set.Icc ((k:ℝ) * Δt) (((k:ℝ) + 1) * Δt) :=
    ⟨by linarith [hσ.1], by rw [hexpand]; linarith [hσ.2]⟩
  rw [hu _ hmem]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
