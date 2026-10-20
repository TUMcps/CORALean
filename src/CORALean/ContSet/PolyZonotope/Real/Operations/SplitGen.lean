module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SplitLongestIndepGen

@[expose] public section

/-!
# `PolyZonotope.splitGen`

`containsPointSet` calls `splitLongestGen` and, when it throws (no dependent generator),
`aux_splitLongestIndepGen`. `splitGen` is that `try ... catch`, `splitLongestGen`'s own `none`
(no dependent generator or no factor) being sent to the independent split.

## Inputs
* `pZ` – polynomial zonotope

## Output
* pair of polynomial zonotopes from splitting the longest generator
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.splitGen (pZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ n) × PolyZonotope (Vec ℝ n) :=
  match pZ.longestFactor with
  | some k => pZ.splitDepFactor k
  | none => pZ.splitLongestIndepGen

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
