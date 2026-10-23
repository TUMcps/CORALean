module

public import CORALean.Specification.STLInterval.Definitions.RepresentsaType
public import CORALean.Specification.STLInterval.Definitions.WithinTol

@[expose] public section

/-!
# `representsa_` of an STL interval

`@stlInterval/representsa_.m`: the empty interval (`representsa_emptyObject`) is an `'emptySet'`
and an `'stlInterval'`, not a `'point'` or the `'origin'`; every interval is an `'stlInterval'`;
any other type is answered by the closed box `interval(I)`, and is `false` for an interval with an
open end. A point has `rad(I) = (upper - lower)/2` within `tol` of `0`, the origin both bounds.

## Inputs
* `tol` – tolerance

## Output
* the interval represents the given set type up to the tolerance
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.representsa_ (tol : ℝ) : STLInterval 𝕋 → STLInterval.RepresentsaType → Prop
  | .empty, .emptySet => True
  | .empty, .stlInterval => True
  | .empty, _ => False
  | .nonempty .., .stlInterval => True
  | .nonempty .., .emptySet => False
  | .nonempty l u lc rc _ _ _, .point =>
    lc = true ∧ rc = true ∧ ∃ y : ℝ, toEReal u = y ∧ withinTol tol ((y - toReal l) / 2 : ℝ) 0
  | .nonempty l u lc rc _ _ _, .origin =>
    lc = true ∧ rc = true ∧ withinTol tol (toReal l : ℝ) 0 ∧ withinTol tol (toEReal u) 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
