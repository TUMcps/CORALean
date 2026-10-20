module

public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# `eqScalar`: equality certified by two comparisons

Two scalars with `le` both ways. `le` is sound when `true`, so `true` here says the two read
as the same real; `false` says nothing. The exact test `compact_` needs for "equal rows".

## Inputs
* `a` – scalar
* `b` – scalar

## Output
* both `le a b` and `le b a`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both `le a b` and `le b a`. -/
def HPolytope.eqScalar (a b : 𝕋) : Bool := le a b && le b a

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
