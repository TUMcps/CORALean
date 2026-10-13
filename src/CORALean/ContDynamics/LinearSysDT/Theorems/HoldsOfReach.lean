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

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.holds_of_reach (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o) (R₀ U : S n)
    (spec : Specification ContSet) {x u : ℕ → Vec ℝ n}
    (traj : sys.Trajectory R₀ U x u) (k : ℕ)
    (h : spec.Holds (construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩))) : spec.Holds {x k} :=
  spec.holds_of_outer (Set.singleton_subset_iff.mpr (sys.reach_outer ho R₀ U traj k)) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
