module

public import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachSetForall

@[expose] public section

/-!
# Every run from the backward reachable set lands in the target

What makes `backReachSetForall` deserve the name: a trajectory that starts in
the `k`-step set is in `T` at step `k`, whatever inputs `U` handed it. `R₀`
goes unused — where a run began says nothing about where it must end, and
`simulate_trajectory` builds a `Trajectory` from any starting point at all.

The induction runs on the step count with the start time left free, since
`backReachSetForall` peels a step off the *front* of a run while `Trajectory`
is stated from time zero. `aux_backReachSetForall_from` is that general form,
and the theorem below is it at time zero.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The same statement from an arbitrary time `j`, which is what the induction
on `k` needs: one step forward moves the start, not the target. -/
theorem LinearSysDT.aux_backReachSetForall_from (sys : LinearSysDT 𝕋 n) (T U : S n)
    {R₀ : S n} {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (k : ℕ) :
    ∀ j, x j ∈ sys.backReachSetForall T U k → x (j + k) ∈ construct T := by -- --- PROOF ---
  induction k with
  | zero => exact fun j hj => hj
  | succ k ih =>
    intro j hj
    -- the input at time `j` is one of those the `∀` reading quantified over
    have hnext : x (j + 1) ∈ sys.backReachSetForall T U k := by
      rw [traj.step j]
      exact hj (u j) (traj.input j)
    have h := ih (j + 1) hnext
    rwa [show j + 1 + k = j + (k + 1) by omega] at h


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.backReachSetForall_trajectory (sys : LinearSysDT 𝕋 n) (T U : S n)
    {R₀ : S n} {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (k : ℕ)
    (hx : x 0 ∈ sys.backReachSetForall T U k) : x k ∈ construct T := by
  have h := sys.aux_backReachSetForall_from T U traj k 0 hx
  rwa [Nat.zero_add] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
