import CORALean.ContSet.PolyZonotope.Real.Operations.SplitLongestGen
import CORALean.ContSet.PolyZonotope.Real.Theorems.SplitDepFactorUnion

/-!
# The halves of `splitLongestGen` cover the set, exactly

Whichever factor the heuristic picks, `splitDepFactor_union` applies; with no factor the two
halves are the set itself.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.splitLongestGen_union (pZ : PolyZonotope (Vec ℝ n)) :
    pZ.splitLongestGen.1.construct ∪ pZ.splitLongestGen.2.construct = pZ.construct := by
  unfold PolyZonotope.splitLongestGen
  cases pZ.longestFactor with
  | some k => exact pZ.splitDepFactor_union k
  | none => exact Set.union_self _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
