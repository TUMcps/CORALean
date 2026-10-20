module

public import CORALean.ContSet.ConPolyZono.Real.Operations.SplitDepFactor
public import CORALean.ContSet.ConPolyZono.Real.Operations.LongestFactor

@[expose] public section

/-!
# `ConPolyZono.splitLongestGen`

CORA's `@conPolyZono/splitLongestGen`: `splitDepFactor` at the factor `longestFactor` picks.
CORA also returns the factor; it is `longestFactor`. A set with no factor to split is returned
twice, where CORA's `max` of an empty vector errors.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Output
* two halves split along the longest generator
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two halves of `cPZ` along the factor of its longest generators. -/
noncomputable def ConPolyZono.splitLongestGen (cPZ : ConPolyZono (Vec ℝ n)) :
    ConPolyZono (Vec ℝ n) × ConPolyZono (Vec ℝ n) :=
  match cPZ.longestFactor with
  | some r => cPZ.splitDepFactor r
  | none => (cPZ, cPZ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
