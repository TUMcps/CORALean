module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `MatExp.normUpperBound`, a float upper bound of a dominating norm

`Real.Interval.absMax`'s entrywise formula, `max |inf| |sup|`, row-summed by
`radius` and maxed over rows by `maximumOver` — the same two folds
`expRemainderBound` needs of `‖A.absMax‖`, the `l∞` operator norm being exactly
the largest row sum of absolute entries. Held above `zero` by an exact
`maximum`, so `Theorems/NormUpperBoundFloat` needs no separate nonnegativity
argument.

## Inputs
* `A` – float interval matrix

## Output
* float upper bound of a dominating norm
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.normUpperBound (A : Interval (Mat 𝕋 n n)) : 𝕋 :=
  maximum zero (maximumOver
    (radius fun i j => maximum (absolute (A.inf i j)) (absolute (A.sup i j))))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
