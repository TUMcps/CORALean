import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter
import CORALean.ContDynamics.NonlinearSysDT.Theorems.LinStepLinInputOuter
import CORALean.ContDynamics.NonlinearSysDT.Operations.Linearize
import CORALean.ContDynamics.NonlinearSysDT.Operations.LinInput
import CORALean.ContDynamics.NonlinearSysDT.Operations.Reach
import CORALean.ContDynamics.NonlinearSysDT.Operations.Simulate

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
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {𝕋 : Type} [CORALean.Float.FloatOps 𝕋] [CORALean.Float.SoundFloatArithmetic 𝕋]
variable [Mtimes (Mat 𝕋) S] [CORALean.Float.OfInterval S 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reach` contains every trajectory of a run known only up to step `K`, at
every step within it, confined to each step's own certified region. -/
theorem NonlinearSysDT.reach_outer_on (sys : NonlinearSysDT n m) {U : S m} {o : ℕ} (ho : 0 < o)
    (steps : ℕ → sys.LinStep 𝕋 U) (R₀ : S n) {K : ℕ} {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m}
    (traj : sys.TrajectoryOn R₀ U K x u) (hR : ∀ k < K, x k ∈ (steps k).R) :
    ∀ k ≤ K, x k ∈ construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps) := by -- --- PROOF ---
  -- the induction is on the step count, one linearization spent per step
  intro k
  induction k with
  | zero => intro _; exact traj.init
  | succ k ih =>
    intro hk
    have hkK : k < K := Nat.lt_of_succ_le hk
    show x (k + 1) ∈ construct ((NonlinearSysDT.linearize (steps k).A).reach
      ⟨sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps, (steps k).linInput, 0, 1⟩ ⟨o, ho⟩)
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
