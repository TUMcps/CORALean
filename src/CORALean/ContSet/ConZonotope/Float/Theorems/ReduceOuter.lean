import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
import CORALean.ContSet.ConZonotope.Float.Operations.Reduce
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOuter

/-!
# `ConZonotope.reduce` over-approximates

Above the order it is the zonotope's `reduce` composed with forgetting the
constraints, both enclosures; at or below it, the identity.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduce_outer (cZ : ConZonotope 𝕋 n) (o : ℕ) :
    cZ.construct ⊆ (cZ.reduce o).construct := by -- --- PROOF ---
  unfold ConZonotope.reduce
  split_ifs with hlt
  · exact subset_trans (subset_trans (ConZonotope.zonotope_contains cZ)
      (Zonotope.reduce_outer cZ.zonotope o)) (Zonotope.conZonotope_contains _)
  · exact subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
