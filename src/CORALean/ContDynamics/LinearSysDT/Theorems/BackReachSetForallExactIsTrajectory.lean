module

public import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachSetForallExact

@[expose] public section

/-!
# Every run from the backward reachable set lands in the target

What makes `backReachSetForallExact` deserve the name: a trajectory that starts in the `k`-step set
is in `T` at step `k`, whatever inputs `U` handed it. `R₀` goes unused — where a run began says
nothing about where it must end. The induction runs on the step count with the start time left
free, since `backReachSetForallExact` peels a step off the *front* of a run while `IsTrajectory`
is stated from time zero; `aux_backReachSetForallExact_from` is that general form.

## Inputs
* `sys` – system
* `T` – target set
* `U` – input set
* `R₀` – initial set
* `x` – trajectory
* `u` – input signal
* `k` – step

## Hypotheses
* `traj` – discrete-time trajectory
* `hx` – start lies in the backward reachable set

## Conclusion
* the run is in the target at step `k`
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
theorem LinearSysDT.aux_backReachSetForallExact_from (sys : LinearSysDT 𝕋 n) (T U : S n)
    {R₀ : S n} {x u : ℕ → Vec ℝ n} (traj : sys.IsCanonicalTrajectory R₀ U x u)
    (k : ℕ) : -- --- CONCL ---
    ∀ j, x j ∈ sys.backReachSetForallExact T U k → x (j + k) ∈ construct T := by -- --- PROOF ---
  induction k with
  | zero => exact fun j hj => hj
  | succ k ih =>
    intro j hj
    -- the input at time `j` is one of those the `∀` reading quantified over
    have hnext : x (j + 1) ∈ sys.backReachSetForallExact T U k := by
      rw [traj.step j]
      exact hj (u j) (traj.input j)
    have h := ih (j + 1) hnext
    rwa [show j + 1 + k = j + (k + 1) by omega] at h


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.backReachSetForallExact_isTrajectory (sys : LinearSysDT 𝕋 n) (T U : S n)
    {R₀ : S n} {x u : ℕ → Vec ℝ n} (traj : sys.IsCanonicalTrajectory R₀ U x u) (k : ℕ)
    (hx : x 0 ∈ sys.backReachSetForallExact T U k) : x k ∈ construct T := by
  have h := sys.aux_backReachSetForallExact_from T U traj k 0 hx
  rwa [Nat.zero_add] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
