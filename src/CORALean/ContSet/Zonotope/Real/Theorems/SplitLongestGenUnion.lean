module

public import CORALean.ContSet.Zonotope.Real.Operations.SplitLongestGen
public import CORALean.ContSet.Zonotope.Real.Theorems.SplitUnion

@[expose] public section

/-!
# Splitting at the longest generator loses nothing

`splitLongestGen`'s halves cover the zonotope exactly: `split_union` at the chosen index, or, with
no generator, the zonotope itself twice.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.splitLongestGen_union (Z : Zonotope (Vec ℝ n)) :
    Z.splitLongestGen.1.construct ∪ Z.splitLongestGen.2.construct =
      Z.construct := by
  unfold Zonotope.splitLongestGen
  cases Z.longestGen with
  | some j => exact Z.split_union j
  | none => exact Set.union_self _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
