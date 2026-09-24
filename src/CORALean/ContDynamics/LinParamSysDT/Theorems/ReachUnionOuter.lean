import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachUnionExact
import CORALean.ContDynamics.LinParamSysDT.Operations.ReachUnion
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachSetOfInitSubsetReach
import CORALean.ContSet.SetUnion.SetUnion

/-!
# `reachUnion` encloses `reachUnionExact`

Every step's inclusion, `reachSetOfInit_subset_reach`, landing in its own
branch of the `SetUnion`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Reduce Mtimes

variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.WithInput.reachUnion_outer (sys : LinParamSysDT.WithInput 𝕄 S n)
    (p : LinParamSysDT.ReachParams) (X₀ : S n) :
    sys.reachUnionExact p (construct X₀) ⊆ construct (sys.reachUnion p X₀) := by -- --- PROOF ---
  intro y hy
  obtain ⟨k, hk, hy⟩ := Set.mem_iUnion₂.mp hy
  refine SetUnion.mem_construct.mpr ⟨sys.sys.reach p.o p.ho X₀ sys.U k, ?_,
    sys.reachSetOfInit_subset_reach p X₀ k hy⟩
  exact List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le hk))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
