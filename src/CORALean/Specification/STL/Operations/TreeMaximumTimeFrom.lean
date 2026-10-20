module

public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# The latest time a formula looks at

`@stl/maximumTime.m`, `aux_recursive(obj,time)`: `time` is the offset accumulated by the `next`
operators above; the bound of a `finally`, `globally`, `until` or `release` is added to the
largest time its operands need. CORA first returns `time` for every non-temporal sub-formula; the
clauses for `~`, `&` and `|` give the same value, so the test is not repeated
(`STL.Tree.maximumTimeFrom_of_not_temporal`). Real-only, a specification: the exact latest time a
formula reads.

## Inputs
* none

## Output
* the latest time the formula looks at
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

/-- `aux_recursive(obj,time)` of `maximumTime.m`. -/
def STL.Tree.maximumTimeFrom : STL.Tree n → ℝ≥0 → ℝ≥0
  | .tt, time | .ff, time | .cmp _ _ _, time => time
  | .not φ, time => φ.maximumTimeFrom time
  | .and φ ψ, time | .or φ ψ, time => max (φ.maximumTimeFrom time) (ψ.maximumTimeFrom time)
  | .next a φ, time => φ.maximumTimeFrom (a + time)
  | .finally _ b φ, time | .globally _ b φ, time => b + φ.maximumTimeFrom time
  | .until _ b φ ψ, time | .release _ b φ ψ, time =>
    b + max (φ.maximumTimeFrom time) (ψ.maximumTimeFrom time)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
