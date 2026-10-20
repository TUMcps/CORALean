module

public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter

@[expose] public section

/-!
# `reachOrders` contains every trajectory

The same induction `reach_outer_on` runs, at `reach_one_outer` once per step — soundness needs
nothing about which order a step reduces to, `reduce_outer` holding at every one, so the sequence
`o` costs the argument nothing past reading `o (k + 1)` off at step `k + 1`. Proved directly
against `IsTrajectory` rather than through a `IsTrajectoryOn` bridge as `ReachOuter.lean` is: that
bridge is an `aux_` lemma local to its own file, and `IsTrajectory`'s fields already hold at every
`k` unconditionally.

## Inputs
* `sys` – system
* `o` – orders per step
* `R₀` – initial set
* `U` – input set
* `x` – trajectory
* `u` – input signal
* `k` – step

## Hypotheses
* `ho` – orders positive
* `traj` – discrete-time trajectory

## Conclusion
* the state at step `k` lies in the reachable set
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reachOrders` contains every trajectory, at every step: `reach_outer` at a
per-step order sequence in place of one fixed order. -/
theorem LinearSysDT.reachOrders_outer (sys : LinearSysDT 𝕋 n) {o : ℕ → ℕ} (ho : ∀ k, 0 < o k)
    (R₀ U : S n) {x u : ℕ → Vec ℝ n} (traj : sys.IsCanonicalTrajectory R₀ U x u)
    (k : ℕ) : -- --- CONCL ---
    x k ∈ construct (sys.reachOrders ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) := by -- --- PROOF ---
  induction k with
  | zero => exact traj.init
  | succ k ih =>
    show x (k + 1) ∈
      construct (sys.reach ⟨sys.reachOrders ⟨R₀, U, 0, k⟩ ⟨o, ho⟩, U, 0, 1⟩ ⟨o (k + 1), ho (k + 1)⟩)
    rw [traj.step k]
    exact sys.reach_one_outer (ho (k + 1)) _ _ ih (traj.input k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
