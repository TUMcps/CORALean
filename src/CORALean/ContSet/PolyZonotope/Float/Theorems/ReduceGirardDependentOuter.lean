import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceGirardDependent
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceByOuter

/-!
# `reduceGirardDependent` over-approximates the set

`reduceBy_outer` holds at every pair of partitions, so it holds at this rule's
own tighter one too.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.reduceGirardDependent_outer (pZ : PolyZonotope (Vec 𝕋 n)) (o : ℕ) :
    pZ.construct ⊆ (pZ.reduceGirardDependent o).construct := by
  unfold PolyZonotope.reduceGirardDependent
  split_ifs with hlt
  · exact PolyZonotope.reduceBy_outer pZ _ _
  · exact subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
