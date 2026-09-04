import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
import CORALean.ContDynamics.NonlinearSys.Theorems.LinInputOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict

/-!
# A nonlinear run is a linear run over a widened input

The handoff conservative linearization exists for: the same state function `x`,
the linear system `linearize A`, and the input signal
`ũ(t) = f(x(t), u(t)) - A x(t)`, which lies in `linInput` wherever the
certificate holds. The flow condition is then an identity — `A x + ũ = f(x,u)`
— and everything `LinearSys` proves applies to `x` unchanged.

The confinement `hR` stays a hypothesis: CORA computes a candidate `R` and
*checks afterwards* that the step's reachable set is inside it, enlarging and
retrying when it is not, which nothing in a certificate can supply.

`hR` is asked for on the time domain and nowhere else, which is why that domain
is a parameter: the linear run produced constrains its input on the same set, so
confinement over one step buys a linear run over one step. `linearize_horizon` is
that instance — restrict to `[0, τ]`, then linearize.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar Plus Mtimes OfInterval

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [OfInterval S]

/-- Every trajectory of `sys` confined to `R` over its own time domain is a
trajectory of `linearize A` over that same domain, with input in `linInput`. -/
theorem NonlinearSys.Trajectory.linearize {sys : NonlinearSys n m} {T : Set ℝ} {R₀ : S n}
    {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {A : Mat ℝ n n}
    {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m} {R : Set (Vec ℝ n)} {L : S n}
    (traj : sys.Trajectory T R₀ U x u)
    (cert : AbstractionError sys.f A B xs us R (construct U) L)
    (hR : ∀ t ∈ T, x t ∈ R) :
    (NonlinearSys.linearize A).Trajectory T R₀ (linInput sys.f A B xs us U L) x
      (fun t => sys.f (x t) (u t) - A *ᵥ x t) where
  init := traj.init
  input t ht := linInput_outer cert (hR t ht) (traj.input t ht)
  flow t ht := by
    have he : toRealMat (NonlinearSys.linearize A).A *ᵥ x t
        + (sys.f (x t) (u t) - A *ᵥ x t) = sys.f (x t) (u t) := by
      show A *ᵥ x t + (sys.f (x t) (u t) - A *ᵥ x t) = sys.f (x t) (u t)
      abel
    show HasDerivWithinAt x (toRealMat (NonlinearSys.linearize A).A *ᵥ x t
      + (sys.f (x t) (u t) - A *ᵥ x t)) T t
    rw [he]
    exact traj.flow t ht

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
