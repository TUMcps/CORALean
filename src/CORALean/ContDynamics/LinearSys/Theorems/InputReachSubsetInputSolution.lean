import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableReflectIoc
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionOuter

/-!
# `inputSolution` contains everything the input can contribute over a step

Thm. 3.1 as a statement about `inputReach`: the enclosure holds for every
admissible input at once, which is the form Prop. 3.3 composes with in
`inputSolution_timeInterval_outer`, and `InputSolutionTimeIntervalOuterSplit`
composes with a second time for its intermediate window.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
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
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] in
theorem LinearSys.inputReach_subset_inputSolution [Mtimes ℐ S]
    (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) {U : S n}
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r η) U))) :
    sys.inputReach U r ⊆ construct (sys.inputSolution r η U) := by -- --- PROOF ---
  rintro _ ⟨u, hmem, hmeas, rfl⟩
  refine sys.inputSolution_outer hr η hε hconv hclosed hbdd hRconv hRclosed hRbdd ?_
    (aestronglyMeasurable_reflect_Ioc hmeas)
  intro σ hσ
  exact hmem _ ⟨by linarith [hσ.2], by linarith [hσ.1]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
