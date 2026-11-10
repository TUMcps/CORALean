module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
public import CORALean.ContSet.Interval.Real.Instances
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# One step of the homogeneous flow, as a set

CORA's `CH(X₀, e^{Ar}X₀) ⊕ F X₀`, over a whole step rather than at its ends: the segment from the
set to its image, widened by what the curvature of the flow adds. Both ends are arguments, the set
`Xₖ` and a set `Xₖ₁` holding its image `e^{AΔt}Xₖ`, so a caller that has the later time-point set
already does not compute it a second time. `linComb` rather than a convex hull, so a non-convex
representation keeps its shape. `exp` needs a norm on `Mat`, which is a
choice rather than an instance, so every file reasoning about this definition must make the same
one, the `l∞` operator norm, or the terms will not match.

## Inputs
* `sys` – linear system
* `Δt` – step length
* `η` – Taylor order
* `Xₖ` – set at the start of the step
* `Xₖ₁` – set at the end of the step

## Output
* set over the whole step: hull of the set and its image widened by the curvature
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `CH(Xₖ, Xₖ₁) ⊕ F Xₖ`, over a whole step rather than at its ends, where `Xₖ₁` holds
`e^{AΔt}Xₖ`. -/
noncomputable def LinearSys.timeInterval
    (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ) (Xₖ Xₖ₁ : S n) : S n :=
  let H := LinComb.linComb Xₖ Xₖ₁                                        -- hull of the two ends
  let C := Mtimes.mtimes (𝕄 := ℐ) (MatExp.correctionMatrix (toRealMat sys.A) Δt η) Xₖ  -- F Xₖ
  H ⊞ C                                                                    -- H ⊕ C

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
