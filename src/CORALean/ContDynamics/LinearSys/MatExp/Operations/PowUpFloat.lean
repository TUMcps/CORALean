import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `MatExp.powUp`, a float upper bound of a nonnegative power

`a ^ k` for a nonnegative `a`, rounded up at every multiplication: what
`expRemainderBound`'s numerator needs of the dominating norm, computed rather
than assumed exact the way `Real.MatExp.expRemainderBound` reads `‖x‖ ^ (η+1)`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.powUp : ℕ → 𝕋 → 𝕋
  | 0, _ => one
  | k + 1, a => mulUp a (MatExp.powUp k a)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
