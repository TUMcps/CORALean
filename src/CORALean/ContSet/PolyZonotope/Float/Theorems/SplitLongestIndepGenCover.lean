import CORALean.ContSet.PolyZonotope.Float.Operations.SplitLongestIndepGen
import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitIndepGenOuter

/-!
# `PolyZonotope.splitLongestIndepGen` covers the set

`splitIndepGen_outer` at whichever generator the float ranking chose, the set being its own
cover where there is none. Outer, not exact.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.splitLongestIndepGen_cover (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.splitLongestIndepGen.1.construct
      ∪ pZ.splitLongestIndepGen.2.construct := by -- --- PROOF ---
  unfold PolyZonotope.splitLongestIndepGen
  dsimp only
  split
  · exact PolyZonotope.splitIndepGen_outer pZ _
  · exact Set.subset_union_left

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
