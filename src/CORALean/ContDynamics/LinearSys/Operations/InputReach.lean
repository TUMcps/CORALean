module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-!
# Every point the input alone can reach

CORA's `P^R(τ)`, and the one definition here that is a plain `Set` rather than a representation:
it is what an enclosure is measured against, so it must not be computed by anything. Stated over
`Icc`, which the reflection `s ↦ τ - s` maps to itself, so the substitution the input solution
runs on costs no endpoint bookkeeping. `exp` needs a norm on `Mat`, which is a choice rather
than an instance, so every file reasoning about this definition must make the same one, the
`l∞` operator norm, or the terms will not match.

## Inputs
* `sys` – linear system
* `U` – input set
* `τ` – time

## Output
* points the input can drive the system to over the interval
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `P^R(τ)`: every point the input can drive the system to over `[0, τ]`,
as a set of points rather than a representation of one. Admissible inputs are
those staying in `U` and measurable enough to integrate, no more. -/
noncomputable def LinearSys.inputReach (sys : LinearSys 𝕋 n) (U : S n) (τ : ℝ) :
    Set (Vec ℝ n) :=
  {y | ∃ u : ℝ → Vec ℝ n,
      (∀ s ∈ Set.Icc (0:ℝ) τ, u s ∈ construct U) ∧
      AEStronglyMeasurable u (volume.restrict (Set.Icc 0 τ)) ∧
      y = ∫ s in (0:ℝ)..τ, exp ((τ - s) • toRealMat sys.A) *ᵥ u s}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
