import CORALean.ContDynamics.LinearSysDT.Definitions.ReachUnionExact
import CORALean.ContDynamics.LinearSysDT.Operations.ReachUnion
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetOfInitEqReachSet
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetSubsetReach
import CORALean.ContSet.SetUnion.SetUnion

/-!
# `reachUnion` encloses `reachUnionExact`

Every step's inclusion, `LinearSysDT.reachSet_subset_reach` read at
`reachSetOfInit_eq_reachSet`, landing in its own branch of the `SetUnion`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Reduce Mtimes

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.WithInput.reachUnion_outer (sys : LinearSysDT.WithInput 𝕋 S n)
    (p : LinearSysDT.ReachParams) (X₀ : S n) :
    sys.reachUnionExact p (construct X₀) ⊆ construct (sys.reachUnion p X₀) := by -- --- PROOF ---
  intro y hy
  obtain ⟨k, hk, hy⟩ := Set.mem_iUnion₂.mp hy
  rw [sys.reachSetOfInit_eq_reachSet] at hy
  refine SetUnion.mem_construct.mpr ⟨sys.sys.reach p.o p.ho X₀ sys.U k, ?_,
    sys.sys.reachSet_subset_reach p.ho X₀ sys.U k hy⟩
  exact List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le hk))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
