module

public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.LinStepLinInputOuter
public import CORALean.ContDynamics.NonlinearSysDT.Operations.Linearize
public import CORALean.ContDynamics.NonlinearSysDT.Operations.LinInput
public import CORALean.ContDynamics.NonlinearSysDT.Operations.Reach
public import CORALean.ContDynamics.NonlinearSysDT.Operations.Simulate

@[expose] public section

/-!
# `reach` contains every trajectory known only up to a bound

Induction on the step count, exactly `LinearSysDT.reach_outer_on`'s: no `shift`
or `restrict` is needed, unlike `NonlinearSys.relinReach_outer`, since a
discrete step already reads `x(k+1) = f(x(k), u(k))` at the step index itself
— nothing to re-anchor onto `[0, Δt]`. `linInput_outer` supplies the one fact
a step needs, in place of the hypothesis `NonlinearSys.relinReach_outer` takes
on `Ud`.

Confinement (`hR`) stays a hypothesis per step, and the asymmetry — below `K`,
never at `K` — is exactly what `confinement_of_subset` needs to discharge it
from a check on the computed sets rather than on the trajectory.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {𝕋 : Type} [CORALean.Float.FloatOps 𝕋] [CORALean.Float.SoundFloatArithmetic 𝕋]
variable [Mtimes (Mat 𝕋) S] [CORALean.Float.OfInterval S 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The run's two defining equations, read off `Nat.fold` by its exported
unfolding lemmas, since a module cannot unfold `Nat.fold` itself. -/
private theorem aux_reach_zero_eq (sys : NonlinearSysDT n m) {U : S m} {o : ℕ} (ho : 0 < o)
    (steps : ℕ → sys.LinStep 𝕋 U) (R₀ : S n) :
    sys.reach ⟨R₀, U, 0, 0⟩ ⟨o, ho⟩ steps = R₀ := by
  show Nat.fold (0 - 0) _ R₀ = R₀
  rw [Nat.sub_self, Nat.fold_zero]

private theorem aux_reach_succ_eq (sys : NonlinearSysDT n m) {U : S m} {o : ℕ} (ho : 0 < o)
    (steps : ℕ → sys.LinStep 𝕋 U) (R₀ : S n) (k : ℕ) : -- --- CONCL ---
    sys.reach ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩ steps
      = (NonlinearSysDT.linearize (steps k).A).reach
        ⟨sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps,
          (steps k).linInput, 0, 1⟩ ⟨o, ho⟩ := by -- --- PROOF ---
  show Nat.fold (k + 1 - 0) _ R₀ = _
  rw [Nat.sub_zero, Nat.fold_succ]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reach` contains every trajectory of a run known only up to step `K`, at
every step within it, confined to each step's own certified region. -/
theorem NonlinearSysDT.reach_outer_on (sys : NonlinearSysDT n m) {U : S m} {o : ℕ} (ho : 0 < o)
    (steps : ℕ → sys.LinStep 𝕋 U) (R₀ : S n) {K : ℕ} {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m}
    {y : ℕ → Vec ℝ sys.q} (traj : sys.IsTrajectoryOn R₀ U K x u y)
    (hR : ∀ k < K, x k ∈ (steps k).R) : -- --- CONCL ---
    ∀ k ≤ K, x k ∈ construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps) := by -- --- PROOF ---
  -- the induction is on the step count, one linearization spent per step
  intro k
  induction k with
  | zero => intro _; rw [aux_reach_zero_eq]; exact traj.init
  | succ k ih =>
    intro hk
    have hkK : k < K := Nat.lt_of_succ_le hk
    rw [aux_reach_succ_eq]
    rw [traj.step k hkK]
    -- the certificate's whole job: `f(x,u) - A x` lies in the widened input
    have hu : sys.f (x k) (u k) - toRealMat (steps k).A *ᵥ x k ∈ construct (steps k).linInput :=
      (steps k).linInput_outer (hR k hkK) (traj.input k hkK)
    have key := LinearSysDT.reach_one_outer (NonlinearSysDT.linearize (steps k).A) ho
      (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps) (steps k).linInput (ih hkK.le) hu
    -- `A x + (f(x,u) - A x)` is `f(x,u)`, so `key` already says what is wanted
    have heq : toRealMat (NonlinearSysDT.linearize (steps k).A).A *ᵥ x k
        + (sys.f (x k) (u k) - toRealMat (steps k).A *ᵥ x k) = sys.f (x k) (u k) := by
      show toRealMat (steps k).A *ᵥ x k + (sys.f (x k) (u k) - toRealMat (steps k).A *ᵥ x k)
        = sys.f (x k) (u k)
      abel
    rwa [heq] at key

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
