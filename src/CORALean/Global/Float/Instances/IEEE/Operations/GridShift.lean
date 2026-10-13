import CORALean.Global.Float.Instances.Dyadic.Operations.Shift
import CORALean.Global.Float.Instances.IEEE.IEEE

/-!
# How many bits a rounding drops

Enough to leave `p` bits, which is `Dyadic.shift`, and enough to raise the exponent to the
smallest subnormal's, `qmin`, whichever is more. The second is what makes a result below the
normal range land on the subnormal grid, where IEEE 754 keeps a fixed step rather than `p` bits.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace IEEE

variable {fmt : IEEEFormat}


-- =====================================  MAIN DEFINITION  ====================================== --

def gridShift (d : Dyadic fmt.p) : ℕ := max d.shift (fmt.qmin - d.exponent).toNat

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
