import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceGirardDependent
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceByOuter

/-!
# `reduceGirardDependent` over-approximates the set

`reduceBy_outer` holds at every pair of partitions, so it holds at this rule's
own tighter one too.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.reduceGirardDependent_outer (PZ : PolyZonotope 𝕋 n) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduceGirardDependent o).construct := by -- --- PROOF ---
  unfold PolyZonotope.reduceGirardDependent
  split_ifs with hlt
  · exact PolyZonotope.reduceBy_outer PZ _ _
  · exact subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
