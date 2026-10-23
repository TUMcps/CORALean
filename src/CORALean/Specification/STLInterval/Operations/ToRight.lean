module

public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `toRight`: the interval to the right

`@stlInterval/toRight.m`: `(upper, ∞)`, or `[upper, ∞)` when the upper end is open. `none` is
CORA's `CORA:emptySet` error on the empty interval; an interval up to `inf` has nothing to its
right.

## Inputs
* none

## Output
* the interval to the right, or none if empty
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   23-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.toRight : STLInterval 𝕋 → Option (STLInterval 𝕋)
  | .empty => none
  | .nonempty _ none _ _ _ _ _ => some .empty
  | .nonempty _ (some u) _ rc _ hlt z =>
    -- the lower bound is at most the stored upper one, so the new lower bound is `≥ 0`
    some (stlInterval u ⊤ (!rc) false (z.trans (by
      rcases hlt with h | ⟨h, -⟩
      exacts [(EReal.coe_lt_coe_iff.mp h).le, (EReal.coe_eq_coe_iff.mp h).le])))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
