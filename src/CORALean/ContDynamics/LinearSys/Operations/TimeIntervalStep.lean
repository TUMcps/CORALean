import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
import CORALean.ContSet.Interval.Real.Instances
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# One step of the homogeneous flow, as a set

CORA's `CH(X₀, e^{Ar}X₀) ⊕ F X₀`, over a whole step rather than at its ends: the
segment from the set to its image, widened by what the curvature of the flow
adds.

`linComb` rather than a convex hull, so a non-convex representation keeps its
shape.

`exp` needs a norm on `Mat`, which is a choice rather than an instance, so every
file reasoning about this definition must make the same one — the `l∞` operator
norm — or the terms will not match.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


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

/-- CORA's `CH(X₀, e^{Ar}X₀) ⊕ F X₀`, over a whole step rather than at its
ends. -/
noncomputable def LinearSys.timeIntervalStep
    (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ) (X₀ : S n) : S n :=
  LinComb.linComb X₀ (Mtimes.mtimes (exp (r • toRealMat sys.A)) X₀) ⊞
    Mtimes.mtimes (𝕄 := ℐ) (MatExp.correctionMatrix (toRealMat sys.A) r η) X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
