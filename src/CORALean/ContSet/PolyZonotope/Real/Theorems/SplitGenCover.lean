module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SplitGen
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SplitLongestIndepGenCover
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SplitDepFactorUnion

@[expose] public section

/-!
# The halves of `splitGen` cover the set

With a dependent factor to split it is `splitDepFactor_union`; without, the independent
split, `splitLongestIndepGen_cover`.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is covered by the two halves
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Whichever way it splits, the halves cover the set. -/
theorem PolyZonotope.splitGen_cover (pZ : PolyZonotope (Vec ℝ n)) :
    pZ.construct ⊆ pZ.splitGen.1.construct ∪ pZ.splitGen.2.construct := by
  unfold PolyZonotope.splitGen
  cases pZ.longestFactor with
  | some k => exact (pZ.splitDepFactor_union k).symm.subset
  | none => exact pZ.splitLongestIndepGen_cover

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
