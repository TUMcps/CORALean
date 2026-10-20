module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-!
# What one input signal contributes over one step

An integral rather than a set: `stepInput` is what a *given* input `u` adds over
step `k`, propagated to the end of that step, which is the quantity a sampled
trajectory has to hand `LinearSysDT` as its discrete input. Enclosing it for
*every* admissible input is `inputSolution`'s job.

`exp` needs a norm on `Mat`, which is a choice rather than an instance, so every
file reasoning about this definition must make the same one — the `l∞` operator
norm — or the terms will not match.

## Inputs
* `sys` – linear system
* `u` – input signal
* `Δt` – step length
* `k` – step index

## Output
* everything the input contributed over the step, propagated to its end
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Everything the input contributed over step `k`, propagated to its end. -/
noncomputable def LinearSys.stepInput (sys : LinearSys 𝕋 n) (u : ℝ → Vec ℝ n) (Δt : ℝ)
    (k : ℕ) : Vec ℝ n :=
  ∫ s in (k * Δt)..((k + 1) * Δt), exp (((k + 1) * Δt - s) • toRealMat sys.A) *ᵥ u s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
