import CORALean.ContSet.ZonoBundle.Real.Operations.Volume
import CORALean.ContSet.ZonoBundle.Real.Theorems.IsBounded

/-!
# A bundle with a member has finite volume

The bundle is compact, so bounded, so of finite Lebesgue measure.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.volume_lt_top (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    zB.volume < ⊤ :=
  (ZonoBundle.isBounded_construct hk).measure_lt_top


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
