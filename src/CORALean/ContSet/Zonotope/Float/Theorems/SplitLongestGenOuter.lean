module

public import CORALean.ContSet.Zonotope.Float.Operations.SplitLongestGen
public import CORALean.ContSet.Zonotope.Float.Theorems.SplitOuter

@[expose] public section

/-!
# The halves of `Zonotope.splitLongestGen` cover the zonotope, over a floating-point scalar

`split_outer` holds at every generator index, so whichever one the float ranking picks is sound;
with no generator the two halves are the zonotope itself.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* zonotope is covered by the two halves
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.splitLongestGen_outer (Z : Zonotope (Vec 𝕋 n)) :
    Z.construct ⊆ Z.splitLongestGen.1.construct ∪ Z.splitLongestGen.2.construct := by
  unfold Zonotope.splitLongestGen
  cases Z.longestGen with
  | some j => exact Z.split_outer j
  | none => exact Set.subset_union_left

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
