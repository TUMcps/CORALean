module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SplitDepFactor
public import CORALean.ContSet.PolyZonotope.Float.Operations.LongestFactor
public import CORALean.ContSet.PolyZonotope.Float.Operations.SplitLongestIndepGen

@[expose] public section

/-!
# `PolyZonotope.splitGen`, over a floating-point scalar

`containsPointSet` calls `splitLongestGen` and, when it throws (no dependent generator),
`aux_splitLongestIndepGen`. `splitGen` is that `try ... catch`, as over ℝ: the halves along the
factor of the longest dependent generator, else along the longest independent generator.

## Inputs
* `pZ` – polynomial zonotope

## Output
* pair of polynomial zonotopes from splitting the longest generator
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.splitGen (pZ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) ×
    PolyZonotope (Vec 𝕋 n) :=
  match pZ.longestFactor with
  | some k => pZ.splitDepFactor k
  | none => pZ.splitLongestIndepGen

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
