module

public import CORALean.ContSet.Zonotope.Real.Operations.ShortestSplit
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy

@[expose] public section

/-!
# `Zonotope.reduceShortest`

CORA's `nnGeneratorReductionLayer`: with more than `k` generators, `shortestSplit` keeps the `k`
shortest and `reduceBy` boxes the rest, `k + n` generators in all; with at most `k` the
zonotope is returned unchanged.

## Inputs
* `Z` – zonotope
* `k` – number of generators kept

## Output
* zonotope of at most `k + n` generators
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.reduceShortest (Z : Zonotope (Vec ℝ n)) (k : ℕ) : Zonotope (Vec ℝ n) :=
  if hlt : k < Z.h then Z.reduceBy (Z.shortestSplit k hlt) else Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
