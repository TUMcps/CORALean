module

public import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachUnionExact
public import CORALean.ContDynamics.LinParamSysDT.Operations.ReachUnion
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachSetExactSubsetReach
public import CORALean.ContSet.SetUnion.SetUnion
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# `reachUnion` encloses `reachUnionExact`

Every step's inclusion, `reachSetExact_subset_reach`, landing in its own branch of the
`SetUnion`.

## Inputs
* `sys` – system
* `params` – reachability parameters with inputs
* `options` – reachability options

## Hypotheses
* none

## Conclusion
* the computed union encloses the exact reachable union
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
      ⊆ construct (sys.reachUnion params options) := by
  intro y hy
  obtain ⟨k, hk, hy⟩ := Set.mem_iUnion₂.mp hy
  exact SetUnion.mem_construct_range (Nat.lt_succ_of_le hk)
    (sys.reachSetExact_subset_reach options.hZonotopeOrder params.X₀ params.U k hy)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
