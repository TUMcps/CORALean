import CORALean.ContSet.Zonotope.Real.Operations.AreAlignedCora
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffAligned

/-!
# `Zonotope.minkDiffExact2dCora`, CORA's two-dimensional `minkDiff`

CORA's `@zonotope/minkDiff.m` on a full-dimensional 2-D minuend whose subtrahend has
generators. l. 117-120 force `method = 'exact'` for `n == 2`, so every call (the default
`'approx'` included) reaches l. 123: if `aux_areAligned` holds, l. 125 returns
`zonotope(minuend.c - subtrahend.c, minuend.G - subtrahend.G)` ("exact solution for aligned sets
according to [1, Prop. 5]"). Otherwise l. 127 calls `aux_minkDiffZono`, which is not modelled
here: `none`. The header documents `'exact'` as the exact difference.

## References

* [1] `contSet/@zonotope/minkDiff.m`, CORA, ll. 117-127.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- The aligned branch of the forced `'exact'` path; `none` is `aux_minkDiffZono` (not modelled). -/
noncomputable def Zonotope.minkDiffExact2dCora (minuend subtrahend : Zonotope (Vec ℝ 2)) :
    Option (Zonotope (Vec ℝ 2)) :=
  if hh : minuend.h = subtrahend.h then
    -- l. 123: `if aux_areAligned(minuend, subtrahend)`
    if minuend.areAlignedCora subtrahend hh then
      -- l. 125: `zonotope(minuend.c - subtrahend.c, minuend.G - subtrahend.G)`
      some (minuend.minkDiffAligned subtrahend hh)
    else none
  else none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
