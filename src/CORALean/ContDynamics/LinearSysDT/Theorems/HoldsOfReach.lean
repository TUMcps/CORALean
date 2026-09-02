import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# A specification checked on the reachable set holds along every trajectory

What reachability is computed for, and it is `reach_outer` handed to
`Specification.holds_of_outer` — the same step a network's output set takes, on
the same theorem. Neither knows the other exists; both only produce a superset
of something not computable.

Per step, since that is what `reach` returns. A requirement over a horizon is
this at each `k`, and an unbounded one needs an invariant rather than a longer
list.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]

theorem LinearSysDT.holds_of_reach (sys : LinearSysDT 𝕋 n) (o : ℕ) (R₀ U : S n)
    (spec : Specification (Vec ℝ n)) {x u : ℕ → Vec ℝ n}
    (traj : sys.Trajectory R₀ U x u) (k : ℕ)
    (h : spec.Holds (construct (sys.reach o R₀ U k))) : spec.Holds {x k} :=
  spec.holds_of_outer (Set.singleton_subset_iff.mpr (sys.reach_outer o R₀ U traj k)) h

end CORALean.Real
