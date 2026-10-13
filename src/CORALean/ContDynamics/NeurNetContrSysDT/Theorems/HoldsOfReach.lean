import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# A specification checked on the closed loop's reachable set holds along it

`reach_outer` handed to `Specification.holds_of_outer`, exactly as
`LinearSysDT.holds_of_reach` and `HybridAutomaton.holds_of_invariant` do it. That the
set was produced by a plant and a network alternating is not visible here, and
that is the point of the pivot being one theorem: it only ever sees a superset.

Per step, since that is what `reach` returns. A requirement over a horizon is
this at each `k`.
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

theorem NeurNetContrSysDT.holds_of_reach (sys : NeurNetContrSysDT 𝕋 S n) {o : ℕ} (ho : 0 < o)
    (R₀ : S n) (spec : Specification ContSet) {π : Vec ℝ n → Vec ℝ n} (hπ : sys.contr.Sound π)
    {x : ℕ → Vec ℝ n} (traj : sys.Trajectory π R₀ x) (k : ℕ)
    (h : spec.Holds (construct (sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩))) : spec.Holds {x k} :=
  spec.holds_of_outer (Set.singleton_subset_iff.mpr (sys.reach_outer ho R₀ hπ traj k)) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
