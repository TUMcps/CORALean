module

public import CORALean.ContSet.Zonotope.Float.Operations.ReduceShortest
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByOuter

@[expose] public section

/-!
# `Zonotope.reduceShortest` over-approximates the zonotope

With at most `k` generators the zonotope is returned untouched, otherwise the claim is
`reduceBy_outer` at the partition `shortestSplit` chose.

## Inputs
* `Z` – zonotope
* `k` – number of generators kept

## Hypotheses
* none

## Conclusion
* zonotope is contained in its reduction
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceShortest_outer (Z : Zonotope (Vec 𝕋 n)) (k : ℕ) :
    Z.toSet ⊆ (Z.reduceShortest k).toSet := by
  unfold Zonotope.reduceShortest
  split_ifs with hlt
  · exact Zonotope.reduceBy_outer Z _
  · exact subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
