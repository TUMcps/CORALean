module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Real.Operations.Volume

@[expose] public section

/-!
# A bundle is no larger than any member

The bundle is the intersection of its members, so inside each, and Lebesgue measure is monotone.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.volume_le_member (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) :
    zB.volume ≤ MeasureTheory.volume (zB.Z i).construct :=
  MeasureTheory.measure_mono (SetIntersection.construct_subset_ofFn _ i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
