module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `MatExp.powDown`, a float lower bound of a nonnegative power

`a ^ k` for a nonnegative `a`, rounded down at every multiplication: the lower
end of a Taylor coefficient `r ^ k / k!`, which `powUp` bounds from above.

## Inputs
* none

## Output
* float lower bounds of the nonnegative powers
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.powDown : ℕ → 𝕋 → 𝕋
  | 0, _ => one
  | k + 1, a => mulDown a (MatExp.powDown k a)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
