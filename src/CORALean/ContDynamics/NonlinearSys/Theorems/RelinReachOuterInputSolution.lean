import CORALean.ContDynamics.LinearSys.Theorems.StepInputOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuter

/-!
# The re-linearization loop, each step's input enclosure named

The same as `relinReach_outer`, with each step's input enclosure named rather
than assumed. Step `i`'s integral is enclosed on the original clock — restrict
to `[iΔt, (i+1)Δt]`, linearize there, apply `stepInput_outer` — which is why no
shift appears, unlike in `relinReach_outer`'s own induction.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace Plus Mtimes OfInterval

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSys.Trajectory.relinReach_outer_inputSolution [Mtimes ℐ S]
    {sys : NonlinearSys n m} {T : Set ℝ} {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n}
    {u : ℝ → Vec ℝ m} {steps : ℕ → sys.LinStep U} {Δt : ℝ} {N : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 < Δt)
    (hT : Set.Icc 0 ((N : ℝ) * Δt) ⊆ T)
    (hR : ∀ i < N, ∀ t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt), x t ∈ (steps i).R)
    (η : ℕ) (hε : ∀ i < N, ‖Δt • (steps i).A‖ / ((η : ℝ) + 2) < 1)
    (hconv : ∀ i < N, Convex ℝ (construct (steps i).linInput))
    (hclosed : ∀ i < N, IsClosed (construct (steps i).linInput))
    (hbdd : ∀ i < N, Bornology.IsBounded (construct (steps i).linInput))
    (hRconv : ∀ i < N, Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput)))
    (hRclosed : ∀ i < N, IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput)))
    (hRbdd : ∀ i < N, Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput))) (o : ℕ) :
    ∀ i ≤ N, x ((i : ℝ) * Δt) ∈ construct (sys.relinReach o Δt steps
      (fun i => (NonlinearSys.linearize (steps i).A).inputSolution Δt η
        (steps i).linInput) R₀ i) := by -- --- PROOF ---
  -- everything above is per step, so the loop is `relinReach_outer` plus one enclosure
  refine traj.relinReach_outer hΔt.le hT hR hbdd ?_ o
  intro i hi
  have hlin := (traj.restrict (step_subset_horizon hΔt.le hT hi)).linearize
    (steps i).cert (hR i hi)
  exact hlin.stepInput_outer hΔt η (hε i hi) (hconv i hi) (hclosed i hi) (hbdd i hi)
    (hRconv i hi) (hRclosed i hi) (hRbdd i hi) i subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
