import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.StepInput
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
import CORALean.ContDynamics.LinearSys.Theorems.StepInputShift

/-!
# `inputSolution` contains what the input contributed over a step

Althoff's Thm. 3.1 applied to a trajectory, which is what turns the sampled
guarantees' input enclosure from a hypothesis into a theorem.

Every step has the same length, so the enclosing set does not depend on `k`:
shifting `u` by `kΔt` leaves an integral over `[0, Δt]` of the same shape, and
`inputSolution Δt η U` covers every step at once.

The cost is convexity and closedness of `U`, which `ContSet` does not offer; a
representation that cannot supply them keeps the general form, where the
enclosure stays a hypothesis.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

omit [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] in
set_option maxHeartbeats 400000 in
/-- What a step's input contributed lies in `inputSolution`, for every step.

`c := (k+1)Δt` is where the step ends, and reflecting about it is what the
substitution inside `inputSolution_outer` leaves behind — measurable for free,
by `aestronglyMeasurable_input_reflected`. Only step `k` is spoken about, so a
domain covering that step is all the trajectory has to be defined on. -/
theorem LinearSys.Trajectory.stepInput_outer [Mtimes ℐ S]
    {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hΔt : 0 < Δt) (η : ℕ) (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (k : ℕ) (hT : Set.Icc ((k : ℝ) * Δt) (((k : ℝ) + 1) * Δt) ⊆ T) :
    sys.stepInput u Δt k ∈ construct (sys.inputSolution Δt η U) := by
  rw [show ((k : ℝ) + 1) * Δt = (k : ℝ) * Δt + Δt from by ring] at hT
  -- the reflected argument, in the form each lemma states it
  have hrefl : ∀ τ : ℝ, (k : ℝ) * Δt + (Δt - τ) = (k : ℝ) * Δt + Δt - τ := fun τ => by ring
  have hu : ∀ τ ∈ Set.Ioc (0 : ℝ) Δt,
      (fun σ : ℝ => u ((k : ℝ) * Δt + σ)) (Δt - τ) ∈ construct U := by
    intro τ hτ
    exact traj.input _ (hT ⟨by linarith [hτ.2], by linarith [hτ.1]⟩)
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => (fun σ : ℝ => u ((k : ℝ) * Δt + σ)) (Δt - τ))
      (volume.restrict (Set.Ioc 0 Δt)) := by
    simp only [hrefl]
    refine traj.aestronglyMeasurable_input_reflected ?_
    rw [show (k : ℝ) * Δt + Δt - Δt = (k : ℝ) * Δt from by ring]
    exact hT
  rw [sys.stepInput_eq_shifted u Δt k]
  exact sys.inputSolution_outer hΔt η hε hconv hclosed hbdd hRconv hRclosed hRbdd hu hmeas

end CORALean.Real
