import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter

/-!
# `LinearSysDT.reach` contains every trajectory

Induction on the step count, whose step is `reach_one_outer` at the enclosure
the induction hypothesis supplies. The only facts used about `construct` are the
three that theorem uses — `plus_outer`, `reduce_outer` and `mtimes_outer` — so a
representation buys into this by proving those and nothing else.

`reach_outer_on` carries the induction, at a run bounded by `K`; `reach_outer`
is the total case, `K := k` and `le_rfl` away via `toTrajectoryOn`, so nothing
here is proved twice. A bounded run is what `LinearSys.Trajectory
.reach_outer_horizon` produces by sampling on `[0, KΔt]`, and it hands off to
`reach_outer_on` rather than redoing this recursion by hand.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix Pointwise ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] in
/-- A total run restricted to its first `K` steps: nothing past step `K` is
used, so nothing past it needs to hold. -/
theorem LinearSysDT.Trajectory.toTrajectoryOn {sys : LinearSysDT 𝕋 n} {R₀ U : S n}
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (K : ℕ) :
    sys.TrajectoryOn R₀ U K x u where
  init := traj.init
  input k _ := traj.input k
  step k _ := traj.step k

/-- `reach` contains every trajectory of a run known only up to step `K`, at
every step within it. -/
theorem LinearSysDT.reach_outer_on (sys : LinearSysDT 𝕋 n) (o : ℕ) (R₀ U : S n) {K : ℕ}
    {x u : ℕ → Vec ℝ n} (traj : sys.TrajectoryOn R₀ U K x u) :
    ∀ k ≤ K, x k ∈ construct (sys.reach o R₀ U k) := by
  intro k
  induction k with
  | zero => intro _; exact traj.init
  | succ k ih =>
    intro hk
    have hkK : k < K := Nat.lt_of_succ_le hk
    show x (k + 1) ∈ construct (sys.reach o (sys.reach o R₀ U k) U 1)
    rw [traj.step k hkK]
    exact sys.reach_one_outer o _ _ (ih hkK.le) (traj.input k hkK)

theorem LinearSysDT.reach_outer (sys : LinearSysDT 𝕋 n) (o : ℕ) (R₀ U : S n)
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (k : ℕ) :
    x k ∈ construct (sys.reach o R₀ U k) :=
  sys.reach_outer_on o R₀ U (traj.toTrajectoryOn k) k le_rfl

end CORALean.Real
