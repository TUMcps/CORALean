module

public import CORALean.Global.Float.Interfaces
public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# `minimumTime` of a syntax tree over a float scalar: the loop

`aux_recursive(obj,time)` of `minimumTime.m` with the sums of times rounded down and the smaller of
two times taken exactly, so the result is a lower bound of the exact one
(`minimumTimeFromFloat_outer`).

## Inputs
* none

## Output
* a lower bound of the earliest time the formula looks at, counted from `time`
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

/-- `aux_recursive(obj,time)` of `minimumTime.m`, the sums rounded down. -/
def STL.Tree.minimumTimeFromFloat : STL.Tree 𝕋 κ n → 𝕋 → 𝕋
  | .tt, time | .ff, time | .cmp _ _ _, time => time
  | .not φ, time => φ.minimumTimeFromFloat time
  | .and φ ψ, time | .or φ ψ, time =>
    minimum (φ.minimumTimeFromFloat time) (ψ.minimumTimeFromFloat time)
  | .next a φ, time => φ.minimumTimeFromFloat (addDown a time)
  | .finally a _ _, time | .globally a _ _, time => addDown a time
  | .until _ _ _ _, time | .release _ _ _ _, time => time

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
