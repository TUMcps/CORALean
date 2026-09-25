import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `MatExp.powDown`, a float lower bound of a nonnegative power

`a ^ k` for a nonnegative `a`, rounded down at every multiplication: the lower
end of a Taylor coefficient `r ^ k / k!`, which `powUp` bounds from above.
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

def MatExp.powDown : ℕ → 𝕋 → 𝕋
  | 0, _ => one
  | k + 1, a => mulDown a (MatExp.powDown k a)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
