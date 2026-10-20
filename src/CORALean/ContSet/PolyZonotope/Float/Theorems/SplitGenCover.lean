module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SplitGen
public import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitDepFactorOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitLongestIndepGenCover

@[expose] public section

/-!
# `PolyZonotope.splitGen` covers the set

`splitDepFactor_outer` or `splitLongestIndepGen_cover`, whichever branch ran. Outer, not exact.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is covered by the two halves
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Whichever way it splits, the halves cover the set. -/
theorem PolyZonotope.splitGen_cover (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.splitGen.1.construct ∪ pZ.splitGen.2.construct := by
  unfold PolyZonotope.splitGen
  cases pZ.longestFactor with
  | some k => exact PolyZonotope.splitDepFactor_outer pZ k
  | none => exact pZ.splitLongestIndepGen_cover

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
