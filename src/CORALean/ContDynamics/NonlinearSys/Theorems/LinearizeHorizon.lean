import CORALean.ContDynamics.NonlinearSys.Theorems.Linearize

/-!
# A nonlinear run is a linear run over a widened input, one step at a time

The one-step statement: confinement on `[0, τ]` alone yields a linear run on
`[0, τ]`, whatever the nonlinear run does afterwards — the run being longer
than the step costs nothing, `restrict` throwing the rest away. `hR` is asked
for on `[0, τ]` and nowhere else, which is what lets `reach_outer_horizon`
answer for a bounded horizon without a total run.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [OfInterval S]

/-- The one-step statement: confinement on `[0, τ]` alone yields a linear run on
`[0, τ]`, whatever the nonlinear run does afterwards — the run being longer than
the step costs nothing, `restrict` throwing the rest away. -/
theorem NonlinearSys.Trajectory.linearize_horizon {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {A : Mat ℝ n n}
    {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m} {R : Set (Vec ℝ n)} {L : S n} {τ : ℝ}
    (traj : sys.Trajectory T R₀ U x u)
    (cert : AbstractionError sys.f A B xs us R (construct U) L)
    (hT : Set.Icc 0 τ ⊆ T) (hR : ∀ t ∈ Set.Icc (0 : ℝ) τ, x t ∈ R) :
    (NonlinearSys.linearize A).Trajectory (Set.Icc 0 τ) R₀ (linInput sys.f A B xs us U L) x
      (fun t => sys.f (x t) (u t) - A *ᵥ x t) :=
  (traj.restrict hT).linearize cert hR

end CORALean.Real
