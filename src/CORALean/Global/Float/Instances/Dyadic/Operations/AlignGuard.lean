import CORALean.Global.Float.Instances.Dyadic.Dyadic

/-!
# How far below the larger exponent a sum aligns

The widest alignment `addUp`/`addDown` form: well beyond the mantissa width, so that no
operand pair on the `p`-bit grid is coarsened unless the smaller one is far below the ulp of
the sum, yet a constant, so `2 ^ alignGuard p` is small.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def alignGuard (p : ℕ) : ℕ := 4 * p + 64

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
