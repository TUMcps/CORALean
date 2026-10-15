module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGreedy
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxExpMultiCost

@[expose] public section

/-!
# `PolyZonotope.relaxExpGreedyCost`

Asserted, not proved, at `Vec ℝ n`: `Operations/RelaxExpGreedy.lean` runs at most
`N` rounds, each asking the selection `sel` for a pair and applying
`relaxExpMulti` to it. The selection is a parameter of the operation, so its
price `csel` is one here: a round costs at most `csel + relaxExpMultiCost n p`,
and the factor count `p` never changes, a merge keeping it. The generator count
falls by one a round, which the bound ignores.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExpGreedy` costs at `Vec ℝ n` and `p` factors over
`N` rounds, the selection costing at most `csel` per round. -/
def PolyZonotope.relaxExpGreedyCost (n p N : ℕ) (csel : Cost) : Cost :=
  N • (csel + PolyZonotope.relaxExpMultiCost n p)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
