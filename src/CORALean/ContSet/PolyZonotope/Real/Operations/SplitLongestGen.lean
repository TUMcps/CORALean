module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SplitDepFactor
public import CORALean.ContSet.PolyZonotope.Real.Operations.LongestFactor

@[expose] public section

/-!
# `PolyZonotope.splitLongestGen`

CORA's `@polyZonotope/splitLongestGen`: `splitDepFactor` at the factor `longestFactor` picks.
CORA also returns the factor; it is `longestFactor`. A set with no factor to split is returned
twice, where CORA's `max` of an empty vector errors.

## Inputs
* `pZ` – polynomial zonotope

## Output
* pair of polynomial zonotopes from splitting the longest factor
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two halves of `pZ` along the factor of its longest generator. -/
noncomputable def PolyZonotope.splitLongestGen (pZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ n) × PolyZonotope (Vec ℝ n) :=
  match pZ.longestFactor with
  | some k => pZ.splitDepFactor k
  | none => (pZ, pZ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
