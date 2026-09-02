import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
import CORALean.ContDynamics.NonlinearSys.Theorems.LinInputOuter

/-!
# A nonlinear run is a linear run over a widened input

The handoff conservative linearization exists for: the same state function `x`,
the linear system `linearize A`, and the input signal
`ũ(t) = f(x(t), u(t)) - A x(t)`, which lies in `linInput` wherever the
certificate holds. The flow condition is then an identity — `A x + ũ = f(x,u)`
— and everything `LinearSys` proves applies to `x` unchanged.

The confinement hypothesis `hR` is a hypothesis and not something proved here.
CORA computes a candidate `R` from an initial guess and *checks afterwards*
that the step's reachable set is inside it, enlarging and retrying when it is
not; nothing in a certificate can supply that check.

`hR` is asked for on all of `Set.Ici 0`, not on one step `[0, τ]`, and that is
forced rather than chosen: `LinearSys.Trajectory` constrains its input at every
forward time, so a run that leaves `R` after `τ` has no reason to keep `ũ(t)`
inside `linInput` and the conclusion would be false. `linInput_outer` is the
one-step content, stated without any time at all; quantifying it over a
bounded interval instead would need a time-restricted `Trajectory`, which
`LinearSys` does not have.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar Plus Mtimes OfInterval

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [OfInterval S]

/-- Every trajectory of `sys` confined to `R` is a trajectory of `linearize A`
whose input ranges over `linInput`. -/
theorem NonlinearSys.Trajectory.linearize {sys : NonlinearSys n m} {R₀ : S n}
    {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {A : Mat ℝ n n}
    {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m} {R : Set (Vec ℝ n)} {L : S n}
    (traj : sys.Trajectory R₀ U x u)
    (cert : AbstractionError sys A B xs us R (construct U) L)
    (hR : ∀ t : ℝ, 0 ≤ t → x t ∈ R) :
    (NonlinearSys.linearize A).Trajectory R₀ (sys.linInput A B xs us U L) x
      (fun t => sys.f (x t) (u t) - A *ᵥ x t) where
  init := traj.init
  input t ht := NonlinearSys.linInput_outer cert (hR t ht) (traj.input t ht)
  flow t ht := by
    have he : toRealMat (NonlinearSys.linearize A).A *ᵥ x t
        + (sys.f (x t) (u t) - A *ᵥ x t) = sys.f (x t) (u t) := by
      show A *ᵥ x t + (sys.f (x t) (u t) - A *ᵥ x t) = sys.f (x t) (u t)
      abel
    show HasDerivWithinAt x (toRealMat (NonlinearSys.linearize A).A *ᵥ x t
      + (sys.f (x t) (u t) - A *ᵥ x t)) (Set.Ici 0) t
    rw [he]
    exact traj.flow t ht

end CORALean.Real
