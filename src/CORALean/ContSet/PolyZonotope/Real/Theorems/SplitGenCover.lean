import CORALean.ContSet.PolyZonotope.Real.Operations.SplitGen
import CORALean.ContSet.PolyZonotope.Real.Theorems.SplitLongestIndepGenCover
import CORALean.ContSet.PolyZonotope.Real.Theorems.SplitDepFactorUnion

/-!
# The halves of `splitGen` cover the set

With a dependent factor to split it is `splitDepFactor_union`; without, the independent
split, `splitLongestIndepGen_cover`.
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
