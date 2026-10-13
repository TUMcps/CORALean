import CORALean.ContSet.SpectraShadow.Real.Theorems.IsBoundedIff
import CORALean.ContSet.SpectraShadow.Real.Theorems.PointExampleConstruct

/-!
# `SpectraShadow.pointExample_isBounded`

The point `{0}` is bounded, so CORA's `+Inf` support (`supportFuncCoraAllZero_ne_supportFunc`)
calls a bounded set unbounded.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.pointExample_isBounded : SpectraShadow.pointExample.isBounded := by
  rw [SpectraShadow.isBounded_iff, SpectraShadow.pointExample_construct]
  exact (Set.finite_singleton _).isBounded

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
