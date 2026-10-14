module

public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# The earliest time a formula looks at

`@stl/minimumTime.m`, `aux_recursive(obj,time)`: `time` is the offset accumulated by the `next`
operators above. A `finally` or `globally` looks no earlier than its lower bound (CORA does not
add the inner formula's own offset, so this is a lower bound that is not always attained), an
`until` or `release` looks at the present (its left operand holds from time `0`), and `&`, `|`
take the smaller of the two. As for `maximumTime` the test for a non-temporal sub-formula is
folded into the clauses.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_recursive(obj,time)` of `minimumTime.m`. -/
def STL.Tree.minimumTimeFrom : STL.Tree n → ℝ≥0 → ℝ≥0
  | .tt, time | .ff, time | .cmp _ _ _, time => time
  | .not φ, time => φ.minimumTimeFrom time
  | .and φ ψ, time | .or φ ψ, time => min (φ.minimumTimeFrom time) (ψ.minimumTimeFrom time)
  | .next a φ, time => φ.minimumTimeFrom (a + time)
  | .finally a _ _, time | .globally a _ _, time => a + time
  | .until _ _ _ _, time | .release _ _ _ _, time => time

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
