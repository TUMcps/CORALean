module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# A product over a bracket, from below

`a · x` for every `x` a bracket `[lo, hi]` holds, from below: both products and the smaller, which
asks nothing of `a`'s sign — no comparison of stored values establishes one, `le` being
constrained in one direction only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `a * x` from below, for every `x` the bracket `[lo, hi]` holds. -/
def mulRangeDown (a lo hi : 𝕋) : 𝕋 := minimum (mulDown a lo) (mulDown a hi)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
