import CORALean.ContDynamics.NonlinearSys.Theorems.ConfinedOfBall
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuterInputSolution

/-!
# Confinement, discharged from the computed sets

`NonlinearSysDT.confinement_of_subset` gets confinement at step `k` from
`reach_outer_on`, which places `x k` asking confinement strictly below `k`. No
continuous statement does that: `Trajectory.linearize` spends the certificate at
every time of the window it is given, so `relinTimeInterval_outer` needs step
`i`'s own confinement to place `x t` inside step `i`. Checking CORA's
`R([iΔt, (i+1)Δt]) ⊆ R_i` therefore closes no induction on its own.

What does close it is a second ingredient the discrete case has no use for:
`confined_of_ball`, which places the run over a whole step from its value at the
step's start alone. `relinReach_outer_inputSolution` at horizon `i` supplies that
value from confinement below `i`, and the check becomes a ball — inflate step
`i`'s computed set by `ρ > MΔt` and ask that it lie in `R_i`, which is a check on
computed sets and a fatter `R` than CORA's, never on the trajectory.

`M` bounds the field over `R_i`, so it is data of the same kind as the
abstraction error, and `hρ` is strict for the reason `confined_of_ball` is.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
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

/-- Confinement on every step's window, discharged from the computed sets: a
caller checks that each step's computed set, inflated by `ρ > MΔt`, lies in that
step's certified region, instead of assuming confinement of the trajectory. -/
theorem NonlinearSys.Trajectory.confinement_of_subset [Mtimes ℐ S]
    {sys : NonlinearSys n m} {T : Set ℝ} {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n}
    {u : ℝ → Vec ℝ m} {steps : ℕ → sys.LinStep U} {Δt : ℝ} {N : ℕ} {M ρ : ℝ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 < Δt)
    (hT : Set.Icc 0 ((N : ℝ) * Δt) ⊆ T)
    (η : ℕ) (hε : ∀ i < N, ‖Δt • (steps i).A‖ / ((η : ℝ) + 2) < 1)
    (hconv : ∀ i < N, Convex ℝ (construct (steps i).linInput))
    (hclosed : ∀ i < N, IsClosed (construct (steps i).linInput))
    (hbdd : ∀ i < N, Bornology.IsBounded (construct (steps i).linInput))
    (hRconv : ∀ i < N, Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput)))
    (hRclosed : ∀ i < N, IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput)))
    (hRbdd : ∀ i < N, Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (steps i).A Δt η) (steps i).linInput)))
    (hM₀ : 0 ≤ M) (hM : ∀ i < N, ∀ y ∈ (steps i).R, ∀ v ∈ construct U, ‖sys.f y v‖ ≤ M)
    (hρ : M * Δt < ρ) {o : ℕ} (ho : 0 < o)
    (hsub : ∀ i < N, ∀ y ∈ construct (sys.relinReach o ho Δt steps
      (fun i => (NonlinearSys.linearize (steps i).A).inputSolution Δt η (steps i).linInput)
      R₀ i), Metric.closedBall y ρ ⊆ (steps i).R) :
    ∀ i < N, ∀ t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt),
      x t ∈ (steps i).R := by -- --- PROOF ---
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hiN
    -- confinement strictly below `i`, which is all the chain up to `iΔt` asks
    have hRlt : ∀ j < i, ∀ t ∈ Set.Icc ((j : ℝ) * Δt) (((j : ℝ) + 1) * Δt),
        x t ∈ (steps j).R := fun j hj => ih j hj (lt_trans hj hiN)
    have hiNr : (i : ℝ) * Δt ≤ (N : ℝ) * Δt := by
      have : (i : ℝ) ≤ (N : ℝ) := Nat.cast_le.2 hiN.le
      nlinarith
    have hTi : Set.Icc (0 : ℝ) ((i : ℝ) * Δt) ⊆ T :=
      fun t ht => hT ⟨ht.1, le_trans ht.2 hiNr⟩
    -- the chain places `x (iΔt)`, the start of the step, without touching step `i`
    have hstart := traj.relinReach_outer_inputSolution hΔt hTi hRlt η
      (fun j hj => hε j (lt_trans hj hiN)) (fun j hj => hconv j (lt_trans hj hiN))
      (fun j hj => hclosed j (lt_trans hj hiN)) (fun j hj => hbdd j (lt_trans hj hiN))
      (fun j hj => hRconv j (lt_trans hj hiN)) (fun j hj => hRclosed j (lt_trans hj hiN))
      (fun j hj => hRbdd j (lt_trans hj hiN)) ho i le_rfl
    -- and the a priori ball carries it across the step it cannot enclose
    exact traj.confined_of_ball (by nlinarith) (step_subset_horizon hΔt.le hT hiN) hM₀
      (hM i hiN) (by rw [show ((i : ℝ) + 1) * Δt - (i : ℝ) * Δt = Δt from by ring]; exact hρ)
      (hsub i hiN _ hstart)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
