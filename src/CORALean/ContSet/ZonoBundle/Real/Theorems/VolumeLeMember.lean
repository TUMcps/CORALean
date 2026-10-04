import CORALean.ContSet.ZonoBundle.Real.Operations.Volume

/-!
# A bundle is no larger than any member

The bundle is the intersection of its members, so inside each, and Lebesgue measure is monotone.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.volume_le_member (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) :
    zB.volume ≤ MeasureTheory.volume (zB.Z i).construct :=
  MeasureTheory.measure_mono (Set.iInter_subset _ i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
