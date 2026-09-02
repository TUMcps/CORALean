import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter

/-!
# `LinearSysDT.reach` contains every trajectory

Induction on the step count, whose step is `reach_one_outer` at the enclosure
the induction hypothesis supplies. The only facts used about `construct` are the
three that theorem uses — `plus_outer`, `reduce_outer` and `mtimes_outer` — so a
representation buys into this by proving those and nothing else.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix Pointwise ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]

theorem LinearSysDT.reach_outer (sys : LinearSysDT 𝕋 n) (o : ℕ) (R₀ U : S n)
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach o R₀ U k) := by
  induction k with
  | zero => exact traj.init
  | succ k ih =>
    show x (k + 1) ∈ construct (sys.reach o (sys.reach o R₀ U k) U 1)
    rw [traj.step k]
    exact sys.reach_one_outer o _ _ ih (traj.input k)

end CORALean.Real
