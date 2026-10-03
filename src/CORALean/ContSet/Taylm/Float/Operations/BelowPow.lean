import CORALean.Global.Float.FloatOps

/-!
# Checking `x ≤ 2ᵖ/2` in floats

The range `expUp p` is sound on: halve `x` `p` times, which `half` does exactly, and compare
with `1/2`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.belowPow (p : ℕ) (x : 𝕋) : Bool := le (half^[p] x) (half one)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
