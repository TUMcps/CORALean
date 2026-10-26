module

public import CORALean.Global.Float.Interfaces
public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# `maximumTime` of a syntax tree over a float scalar: the loop

`aux_recursive(obj,time)` of `maximumTime.m` with the sums of times rounded up and the larger of
two times taken exactly, so the result is an upper bound of the exact one
(`maximumTimeFromFloat_outer`).

## Inputs
* none

## Output
* an upper bound of the latest time the formula looks at, counted from `time`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps

variable {𝕋 κ : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_recursive(obj,time)` of `maximumTime.m`, the sums rounded up. -/
def STL.Tree.maximumTimeFromFloat : STL.Tree 𝕋 κ n → 𝕋 → 𝕋
  | .tt, time | .ff, time | .cmp _ _ _, time => time
  | .not φ, time => φ.maximumTimeFromFloat time
  | .and φ ψ, time | .or φ ψ, time =>
    maximum (φ.maximumTimeFromFloat time) (ψ.maximumTimeFromFloat time)
  | .next a φ, time => φ.maximumTimeFromFloat (addUp a time)
  | .finally _ b φ, time | .globally _ b φ, time => addUp b (φ.maximumTimeFromFloat time)
  | .until _ b φ ψ, time | .release _ b φ ψ, time =>
    addUp b (maximum (φ.maximumTimeFromFloat time) (ψ.maximumTimeFromFloat time))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
