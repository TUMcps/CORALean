import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# A specification checked on the reachable set holds along every trajectory

`LinearSysDT.holds_of_reach`'s statement, at a system matrix ranging over a
set: `reach_outer` handed to `Specification.holds_of_outer`, the same step a
network's output set takes, on the same theorem.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.holds_of_reach (sys : LinParamSysDT 𝕄 n) (o : ℕ) (R₀ U : S n)
    (spec : Specification (Vec ℝ n)) {x u : ℕ → Vec ℝ n}
    (traj : sys.Trajectory R₀ U x u) (k : ℕ)
    (h : spec.Holds (construct (sys.reach o R₀ U k))) : spec.Holds {x k} :=
  spec.holds_of_outer (Set.singleton_subset_iff.mpr (sys.reach_outer o R₀ U traj k)) h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
