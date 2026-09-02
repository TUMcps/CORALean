import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuter
import CORALean.ContDynamics.LinearSys.Theorems.StepInputOuter
import CORALean.ContDynamics.LinearSys.Theorems.StepInputShift
import CORALean.ContDynamics.NonlinearSys.Operations.RelinReach
import CORALean.ContDynamics.NonlinearSys.Theorems.Linearize
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict
import CORALean.ContDynamics.NonlinearSys.Theorems.Shift

/-!
# The re-linearization loop encloses the run at every step boundary

The composition, and it is one induction on the step count: step `i` is the
one-step guarantee applied to the run re-anchored at `iΔt`, with the enclosure
the induction hypothesis supplies as its initial set. Nothing about step `i`
reaches past its own window, which is what makes the chain a chain rather than
one linearization stretched over a horizon.

Time is handled by re-anchoring, not by absolute windows. Every statement in
`LinearSys` reads `Set.Icc 0 r ⊆ T` and `Trajectory.init` pins `x 0`, so an
absolute window would mean restating all of them; `Trajectory.shift` moves the
run instead and the one-step theorems apply unchanged. The price is a shifted
trajectory in the proof, and it is paid twice — once for the flow, in `Shift`,
and once for the input integral, in `LinearSys.stepInput_shift`, which is what
lets `hUd` below be stated in the original clock rather than in step `i`'s.

Confinement is a hypothesis per step and stays one. CORA computes a candidate
`R` and checks the step's reachable set against it afterwards, enlarging on
failure; no certificate can supply that, and a chain of certificates cannot
either.

`relinReach_outer_inputSolution` names the input enclosure, and it takes the
shorter road: the enclosure of step `i`'s input integral is proved on the
*original* clock, by restricting the run to `[iΔt, (i+1)Δt]` and linearizing
there, so the shift never enters that half of the argument.

Step boundaries only, as `LinearSysDT.reach` gives. Covering the time in between
is `timeIntervalStep` per step, chained the same way, and it is not here: it
would need each step's enclosure at a non-sample time, which `TimeIntervalOuter`
states for one linearization and nothing yet states along a chain.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace Plus Mtimes OfInterval

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S]

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
    (o : ℕ) :
    ∀ i ≤ N, x ((i : ℝ) * Δt) ∈ construct (sys.relinReach o Δt steps Ud R₀ i) := by
  intro i
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
    -- the run re-anchored at the start of step `i`, starting from what step
    -- `i - 1` enclosed
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
    have key := shifted.reach_outer_horizon (K := 1) (steps i).cert hT1 hR1 hΔt
      (hU i hiN) hUd1 o 1 le_rfl
    show x (((i + 1 : ℕ) : ℝ) * Δt) ∈ construct
      (((NonlinearSys.linearize (steps i).A).discretize Δt).reach o
        (sys.relinReach o Δt steps Ud R₀ i) (Ud i) 1)
    rw [show ((i + 1 : ℕ) : ℝ) * Δt = (i : ℝ) * Δt + ((1 : ℕ) : ℝ) * Δt from by
      push_cast; ring]
    exact key

/-- The same with each step's input enclosure named rather than assumed, so the
whole loop is a function of the certificates alone. Step `i`'s integral is
enclosed on the original clock — restrict to `[iΔt, (i+1)Δt]`, linearize there,
apply `stepInput_outer` at step `i` — which is why no shift appears. -/
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
        (steps i).linInput) R₀ i) := by
  refine traj.relinReach_outer hΔt.le hT hR hbdd ?_ o
  intro i hi
  have hlin := (traj.restrict (step_subset_horizon hΔt.le hT hi)).linearize
    (steps i).cert (hR i hi)
  exact hlin.stepInput_outer hΔt η (hε i hi) (hconv i hi) (hclosed i hi) (hbdd i hi)
    (hRconv i hi) (hRclosed i hi) (hRbdd i hi) i subset_rfl

end CORALean.Real
