import CORALean.ContSet.ZonoBundle.Real.Operations.ReduceCombined
import CORALean.ContSet.ZonoBundle.Real.Theorems.EnclosingParallelotopeOuter

/-!
# `ZonoBundle.reduceCombined` over-approximates the bundle

`enclosingParallelotope` encloses the bundle at any edges, so at whichever `n` generators the
filters select.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.reduceCombined_outer (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    zB.construct ⊆ (zB.reduceCombined hk).construct :=
  ZonoBundle.enclosingParallelotope_outer zB hk _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
