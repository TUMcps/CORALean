import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachSet
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter

/-!
# `reach` encloses the reachable set

`reach_outer` restated on `reachSet`: what it says of every run at `k`, this
says of the set of them at once, so a specification about the reachable set
meets the loop's enclosure as a single inclusion.

At every `k`, unlike `NeurNetContrSys`: one plant step and one controller
invocation coincide here, with no period between them for `reachSet` and
`reach` to fall silent over — the gap that theorem's docstring names does not
arise in the purely discrete loop.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this at every step; the guarantee attaches to the reachable set,
not to a run of it. -/
theorem NeurNetContrSysDT.reachSet_subset_reach (sys : NeurNetContrSysDT 𝕋 S n) {o : ℕ}
    (ho : 0 < o) (R₀ : S n) {π : Vec ℝ n → Vec ℝ n} (hπ : sys.contr.Sound π) (k : ℕ) :
    sys.reachSet π R₀ k ⊆ construct (sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩) := by
  rintro _ ⟨x, traj, rfl⟩
  exact sys.reach_outer ho R₀ hπ traj k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
