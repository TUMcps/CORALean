import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable

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
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, OuterContSet (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

/-- Step `k` shifted to start at zero. The propagator only ever sees the elapsed
part of the step, so the shift leaves it alone and lands on exactly the integral
`inputSolution_outer` speaks about. -/
theorem LinearSys.aux_stepInput_eq (sys : LinearSys 𝕋 n) (u : ℝ → Vec ℝ n) (Δt : ℝ) (k : ℕ) :
    sys.stepInput u Δt k
      = ∫ σ in (0:ℝ)..Δt, exp ((Δt - σ) • toRealMat sys.A) *ᵥ u ((k : ℝ) * Δt + σ) := by
  have hsplit : ((k : ℝ) + 1) * Δt = (k : ℝ) * Δt + Δt := by ring
  have hshift : ∀ σ : ℝ, (k : ℝ) * Δt + Δt - ((k : ℝ) * Δt + σ) = Δt - σ := fun σ => by ring
  have key := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := Δt)
    (fun s : ℝ => exp (((k : ℝ) * Δt + Δt - s) • toRealMat sys.A) *ᵥ u s) ((k : ℝ) * Δt)
  simp only [add_zero, hshift] at key
  rw [LinearSys.stepInput, hsplit]
  exact key.symm

set_option maxHeartbeats 400000 in
/-- What a step's input contributed lies in `inputSolution`, for every step.

`c := (k+1)Δt` is where the step ends, and reflecting about it is what the
substitution inside `inputSolution_outer` leaves behind — measurable for free,
by `aestronglyMeasurable_input_reflected`. -/
theorem LinearSys.Trajectory.stepInput_outer [Mtimes ℐ S]
    {sys : LinearSys 𝕋 n}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.Trajectory R₀ U x u)
    (hΔt : 0 < Δt) (η : ℕ) (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (k : ℕ) :
    sys.stepInput u Δt k ∈ construct (sys.inputSolution Δt η U) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) * Δt := mul_nonneg (Nat.cast_nonneg k) hΔt.le
  -- the reflected argument, in the form each lemma states it
  have hrefl : ∀ τ : ℝ, (k : ℝ) * Δt + (Δt - τ) = (k : ℝ) * Δt + Δt - τ := fun τ => by ring
  have hu : ∀ τ ∈ Set.Ioc (0 : ℝ) Δt,
      (fun σ : ℝ => u ((k : ℝ) * Δt + σ)) (Δt - τ) ∈ construct U := by
    intro τ hτ
    exact traj.input _ (by linarith [hτ.2])
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => (fun σ : ℝ => u ((k : ℝ) * Δt + σ)) (Δt - τ))
      (volume.restrict (Set.Ioc 0 Δt)) := by
    simp only [hrefl]
    exact traj.aestronglyMeasurable_input_reflected (by linarith)
  rw [sys.aux_stepInput_eq u Δt k]
  exact sys.inputSolution_outer hΔt η hε hconv hclosed hbdd hRconv hRclosed hRbdd hu hmeas

end CORALean.Real
