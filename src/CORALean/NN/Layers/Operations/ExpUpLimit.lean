module

public import CORALean.Global.Float.Exp

@[expose] public section

/-!
# The largest argument `expUp` is asked for

`2 ^ k / 2` underestimated by doubling `half one` downward, so a float that compares at or below it
is at or below `2 ^ k / 2`, which is `expUp k`'s hypothesis.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   08-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `2 ^ k / 2`, each doubling rounded down. -/
def expUpLimit : ℕ → 𝕋
  | 0 => half one
  | k + 1 => addDown (expUpLimit k) (expUpLimit k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
