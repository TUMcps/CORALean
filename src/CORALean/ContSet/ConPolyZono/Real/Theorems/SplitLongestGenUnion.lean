module

public import CORALean.ContSet.ConPolyZono.Real.Operations.SplitLongestGen
public import CORALean.ContSet.ConPolyZono.Real.Theorems.SplitDepFactorUnion

@[expose] public section

/-!
# The halves of `splitLongestGen` cover the set, exactly

Whichever factor the heuristic picks, `splitDepFactor_union` applies; with no factor the two
halves are the set itself.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* the two halves together are exactly the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.splitLongestGen_union (cPZ : ConPolyZono (Vec ℝ n)) :
    cPZ.splitLongestGen.1.construct ∪ cPZ.splitLongestGen.2.construct = cPZ.construct := by
  unfold ConPolyZono.splitLongestGen
  cases cPZ.longestFactor with
  | some r => exact cPZ.splitDepFactor_union r
  | none => exact Set.union_self _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
