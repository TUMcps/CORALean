module

public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter

@[expose] public section

/-!
# `reach` contains every trajectory known only up to a bound

Induction on the step count, whose step is `reach_one_outer` at the enclosure
the induction hypothesis supplies. The only facts used about `construct` are
the three that theorem uses — `plus_outer`, `reduce_outer` and `mtimes_outer`
— so a representation buys into this by proving those and nothing else.

A bounded run is what `LinearSys.IsCanonicalTrajectory.reach_outer_horizon` produces by
sampling on `[0, KΔt]`, and it hands off to this rather than redoing the
recursion by hand.

## Inputs
* `sys` – system
* `o` – maximum zonotope order
* `R₀` – initial set
* `U` – input set
* `K` – step bound
* `x` – trajectory
* `u` – input signal

## Hypotheses
* `ho` – order positive
* `traj` – trajectory known up to `K`

## Conclusion
* every state up to step `K` lies in the reachable set
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `reach` contains every trajectory of a run known only up to step `K`, at
every step within it. -/
theorem LinearSysDT.reach_outer_on (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o) (R₀ U : S n)
    {K : ℕ} {x u : ℕ → Vec ℝ n} (traj : sys.IsCanonicalTrajectoryOn R₀ U K x u) : -- --- CONCL ---
    ∀ k ≤ K, x k ∈ construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro _; exact traj.init
  | succ k ih =>
    intro hk
    have hkK : k < K := Nat.lt_of_succ_le hk
    show x (k + 1) ∈ construct (sys.reach ⟨sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩, U, 0, 1⟩ ⟨o, ho⟩)
    rw [traj.step k hkK]
    exact sys.reach_one_outer ho _ _ (ih hkK.le) (traj.input k hkK)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
