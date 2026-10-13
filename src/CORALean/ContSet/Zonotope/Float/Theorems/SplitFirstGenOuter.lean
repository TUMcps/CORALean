import CORALean.ContSet.Zonotope.Float.Operations.SplitFirstGen
import CORALean.ContSet.Zonotope.Float.Theorems.SplitOuter

/-!
# The halves of `Zonotope.splitFirstGen` cover the zonotope, over a floating-point scalar

`split_outer` holds at every generator index, so whichever one the ranking picks is sound; with no
generator the two halves are the zonotope itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.splitFirstGen_outer (Z : Zonotope (Vec 𝕋 n)) :
    Z.construct ⊆ Z.splitFirstGen.1.construct ∪ Z.splitFirstGen.2.construct := by -- --- PROOF ---
  unfold Zonotope.splitFirstGen
  dsimp only
  split
  · exact Z.split_outer _
  · exact Set.subset_union_left

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
