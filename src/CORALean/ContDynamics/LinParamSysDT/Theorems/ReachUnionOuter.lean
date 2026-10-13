module

public import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachUnionExact
public import CORALean.ContDynamics.LinParamSysDT.Operations.ReachUnion
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachSetSubsetReach
public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# `reachUnion` encloses `reachUnionExact`

Every step's inclusion, `reachSet_subset_reach`, landing in its own branch of the
`SetUnion`.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Reduce Mtimes

variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.reachUnion_outer (sys : LinParamSysDT 𝕄 n)
    (params : Reach.InputParams (S n) (S n) ℕ) (options : LinParamSysDT.ReachOptions) :
    sys.reachUnionExact params.X₀ params.U (params.tFinal - params.tStart)
      ⊆ construct (sys.reachUnion params options) := by -- --- PROOF ---
  intro y hy
  obtain ⟨k, hk, hy⟩ := Set.mem_iUnion₂.mp hy
  refine SetUnion.mem_construct.mpr ⟨sys.reach ⟨params.X₀, params.U, 0, k⟩ options, ?_,
    sys.reachSet_subset_reach options.hZonotopeOrder params.X₀ params.U k hy⟩
  exact List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le hk))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
