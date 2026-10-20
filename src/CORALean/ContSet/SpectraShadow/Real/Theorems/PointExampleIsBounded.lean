module

public import CORALean.ContSet.SpectraShadow.Real.Theorems.IsBoundedIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.PointExampleConstruct

@[expose] public section

/-!
# `SpectraShadow.pointExample_isBounded`

The point `{0}` is bounded, so CORA's `+Inf` support (`supportFuncCoraAllZero_ne_supportFunc`)
calls a bounded set unbounded.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the point example `{0}` is bounded
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
