import CORALean.ContDynamics.NonlinearSys.Operations.LinStepLinInput
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterHorizon
import CORALean.ContDynamics.LinearSys.Theorems.StepInputOuter
import CORALean.ContDynamics.LinearSys.Theorems.StepInputShift
import CORALean.ContDynamics.LinearSys.Theorems.StepSubsetHorizon
import CORALean.ContDynamics.NonlinearSys.Operations.RelinReach
import CORALean.ContDynamics.NonlinearSys.Theorems.Linearize
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuterHorizon
import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict
import CORALean.ContDynamics.NonlinearSys.Theorems.Shift

/-!
# The re-linearization loop encloses the run at every step boundary

One induction on the step count: step `i` is the one-step guarantee applied to
the run re-anchored at `iΔt`, with what the induction hypothesis encloses as its
initial set. Nothing about step `i` reaches past its own window.

Time is handled by re-anchoring rather than by absolute windows. Every statement
in `LinearSys` reads `Set.Icc 0 r ⊆ T` and `Trajectory.init` pins `x 0`, so
`Trajectory.shift` moves the run and the one-step theorems apply unchanged. The
price is a shifted trajectory, paid once for the flow in `Shift` and once for the
input integral in `LinearSys.stepInput_shift`.

Confinement is a hypothesis per step, asked on that step's own window alone.
`confinement_of_subset` discharges it from a check on the computed sets, so a
caller need not already know where the run goes in order to use this.

Step boundaries only in this file; `relinTimeInterval_outer` covers the time
between them, each step's enclosure at every time rather than just its ends.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace Plus Mtimes Real.OfInterval

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Real.OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run confined step by step is inside `relinReach` at every step boundary of
the horizon. Each step asks for confinement on its own window only, so a chain
of `N` steps never speaks about the run past `NΔt`. -/
theorem NonlinearSys.Trajectory.relinReach_outer {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {steps : ℕ → sys.LinStep U} {Ud : ℕ → S n} {Δt : ℝ} {N : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ Δt)
    (hT : Set.Icc 0 ((N : ℝ) * Δt) ⊆ T)
    (hR : ∀ i < N, ∀ t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt), x t ∈ (steps i).R)
    (hU : ∀ i < N, Bornology.IsBounded (construct (steps i).linInput))
    (hUd : ∀ i < N, (NonlinearSys.linearize (steps i).A).stepInput
      (fun t => sys.f (x t) (u t) - (steps i).A *ᵥ x t) Δt i ∈ construct (Ud i))
    {o : ℕ} (ho : 0 < o) :
    ∀ i ≤ N,
      x ((i : ℝ) * Δt) ∈ construct (sys.relinReach o ho Δt steps Ud R₀ i) := by -- --- PROOF ---
  intro i
  -- the induction is on the step count, every hypothesis being asked per step
  induction i with
  | zero =>
    intro _
    show x (((0 : ℕ) : ℝ) * Δt) ∈ construct R₀
    simpa using traj.init
  | succ i ih =>
    intro hi
    have hiN : i < N := Nat.lt_of_succ_le hi
    have hexp : ((i : ℝ) + 1) * Δt = (i : ℝ) * Δt + Δt := by ring
    have hwin : Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt) ⊆ T :=
      step_subset_horizon hΔt hT hiN
    -- the run re-anchored at the start of step `i`, from what step `i - 1` enclosed
    have hmaps : Set.MapsTo (fun t => (i : ℝ) * Δt + t) (Set.Icc (0 : ℝ) Δt) T := by
      intro t ht
      refine hwin ⟨by linarith [ht.1], ?_⟩
      rw [hexp]
      linarith [ht.2]
    have shifted := traj.shift hmaps (ih hiN.le)
    have hT1 : Set.Icc (0 : ℝ) (((1 : ℕ) : ℝ) * Δt) ⊆ Set.Icc (0 : ℝ) Δt := by
      simp
    have hR1 : ∀ t ∈ Set.Icc (0 : ℝ) (((1 : ℕ) : ℝ) * Δt),
        x ((i : ℝ) * Δt + t) ∈ (steps i).R := by
      intro t ht
      have ht2 : t ≤ Δt := by simpa using ht.2
      refine hR i hiN _ ⟨by linarith [ht.1], ?_⟩
      rw [hexp]
      linarith
    -- step `i`'s input enclosure, moved from the original clock onto the shifted one
    have hUd1 : ∀ k < 1, (NonlinearSys.linearize (steps i).A).stepInput
        (fun t => sys.f (x ((i : ℝ) * Δt + t)) (u ((i : ℝ) * Δt + t))
          - (steps i).A *ᵥ x ((i : ℝ) * Δt + t)) Δt k ∈ construct (Ud i) := by
      intro k hk
      obtain rfl : k = 0 := Nat.lt_one_iff.mp hk
      have hshift := (NonlinearSys.linearize (steps i).A).stepInput_shift
        (fun s => sys.f (x s) (u s) - (steps i).A *ᵥ x s) Δt i
      show (NonlinearSys.linearize (steps i).A).stepInput
        (fun t => (fun s => sys.f (x s) (u s) - (steps i).A *ᵥ x s) ((i : ℝ) * Δt + t))
        Δt 0 ∈ construct (Ud i)
      rw [hshift]
      exact hUd i hiN
    -- one step of the linear guarantee, at horizon 1, on the shifted run
    have key := shifted.reach_outer_horizon (K := 1) (steps i).cert hT1 hR1 hΔt
      (hU i hiN) hUd1 ho 1 le_rfl
    show x (((i + 1 : ℕ) : ℝ) * Δt) ∈ construct
      (((NonlinearSys.linearize (steps i).A).discretize Δt).reach
        ⟨sys.relinReach o ho Δt steps Ud R₀ i, Ud i, 0, 1⟩ ⟨o, ho⟩)
    rw [show ((i + 1 : ℕ) : ℝ) * Δt = (i : ℝ) * Δt + ((1 : ℕ) : ℝ) * Δt from by
      push_cast; ring]
    exact key

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
