import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# A specification checked on the reachable set holds along every trajectory

`LinearSysDT.holds_of_reach`'s statement, at a system matrix ranging over a
set: `reach_outer` handed to `Specification.holds_of_outer`, the same step a
network's exact image takes, on the same theorem.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.holds_of_reach (sys : LinParamSysDT 𝕄 n) {o : ℕ} (ho : 0 < o) (R₀ U : S n)
    (spec : Specification ContSet) {x u : ℕ → Vec ℝ n}
    (traj : sys.Trajectory R₀ U x u) (k : ℕ)
    (h : spec.Holds (construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩))) : spec.Holds {x k} :=
  spec.holds_of_outer (Set.singleton_subset_iff.mpr (sys.reach_outer ho R₀ U traj k)) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
