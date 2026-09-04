import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.LinInputOuter
import CORALean.ContDynamics.NonlinearSysDT.Operations

/-!
# `NonlinearSysDT.reach` contains every trajectory

Induction on the step count, exactly `LinearSysDT.reach_outer_on`'s: no `shift`
or `restrict` is needed, unlike `NonlinearSys.relinReach_outer`, since a
discrete step already reads `x(k+1) = f(x(k), u(k))` at the step index itself
— nothing to re-anchor onto `[0, Δt]`. `linInput_outer` supplies the one fact
a step needs, in place of the hypothesis `NonlinearSys.relinReach_outer` takes
on `Ud`.

Confinement (`hR`) stays a hypothesis per step, as in every re-linearization
guarantee here: CORA computes a candidate `R` and checks the step's reachable
set against it afterwards, which no certificate can supply.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S]

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
  [OfInterval S] in
/-- A total run restricted to its first `K` steps. -/
theorem NonlinearSysDT.Trajectory.toTrajectoryOn {sys : NonlinearSysDT n m} {R₀ : S n}
    {U : S m} {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m}
    (traj : sys.Trajectory R₀ U x u) (K : ℕ) : sys.TrajectoryOn R₀ U K x u where
  init := traj.init
  input k _ := traj.input k
  step k _ := traj.step k

/-- `reach` contains every trajectory of a run known only up to step `K`, at
every step within it, confined to each step's own certified region. -/
theorem NonlinearSysDT.reach_outer_on (sys : NonlinearSysDT n m) {U : S m} (o : ℕ)
    (steps : ℕ → sys.LinStep U) (R₀ : S n) {K : ℕ} {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m}
    (traj : sys.TrajectoryOn R₀ U K x u) (hR : ∀ k < K, x k ∈ (steps k).R) :
    ∀ k ≤ K, x k ∈ construct (sys.reach o steps R₀ k) := by
  -- the induction is on the step count, one linearization spent per step
  intro k
  induction k with
  | zero => intro _; exact traj.init
  | succ k ih =>
    intro hk
    have hkK : k < K := Nat.lt_of_succ_le hk
    show x (k + 1) ∈ construct ((NonlinearSysDT.linearize (steps k).A).reach o
      (sys.reach o steps R₀ k) (steps k).linInput 1)
    rw [traj.step k hkK]
    -- the certificate's whole job: `f(x,u) - A x` lies in the widened input
    have hu : sys.f (x k) (u k) - (steps k).A *ᵥ x k ∈ construct (steps k).linInput :=
      linInput_outer (f := sys.f) (steps k).cert (hR k hkK) (traj.input k hkK)
    have key := LinearSysDT.reach_one_outer (NonlinearSysDT.linearize (steps k).A) o
      (sys.reach o steps R₀ k) (steps k).linInput (ih hkK.le) hu
    -- `A x + (f(x,u) - A x)` is `f(x,u)`, so `key` already says what is wanted
    have heq : toRealMat (NonlinearSysDT.linearize (steps k).A).A *ᵥ x k
        + (sys.f (x k) (u k) - (steps k).A *ᵥ x k) = sys.f (x k) (u k) := by
      show (steps k).A *ᵥ x k + (sys.f (x k) (u k) - (steps k).A *ᵥ x k) = sys.f (x k) (u k)
      abel
    rwa [heq] at key

/-- `reach` contains every trajectory of the total run, at every step. -/
theorem NonlinearSysDT.reach_outer (sys : NonlinearSysDT n m) {U : S m} (o : ℕ)
    (steps : ℕ → sys.LinStep U) (R₀ : S n) {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m}
    (traj : sys.Trajectory R₀ U x u) (hR : ∀ k, x k ∈ (steps k).R) (k : ℕ) :
    x k ∈ construct (sys.reach o steps R₀ k) :=
  sys.reach_outer_on o steps R₀ (traj.toTrajectoryOn k) (fun i _ => hR i) k le_rfl

end CORALean.Real
