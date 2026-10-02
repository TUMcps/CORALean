import CORALean.ContSet.Zonotope.Real.Operations.SplitFirstGen
import CORALean.ContSet.Zonotope.Real.Theorems.SplitUnion
/-!
# The halves of `Zonotope.splitFirstGen` are the zonotope

Exact: `split_union` holds at every generator index, and with no generator the two halves are `Z`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.splitFirstGen_union (Z : Zonotope (Vec ℝ n)) :
    Z.splitFirstGen.1.construct ∪ Z.splitFirstGen.2.construct = Z.construct := by -- --- PROOF ---
  unfold Zonotope.splitFirstGen
  dsimp only
  split
  · exact Z.split_union _
  · exact Set.union_self _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
