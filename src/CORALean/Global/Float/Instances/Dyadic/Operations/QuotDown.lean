import CORALean.Global.Float.Instances.Dyadic.Dyadic

/-!
# The quotient, rounded down while dividing

A quotient of dyadics is a general rational, so the direction has to be
chosen while the integers are still there rather than afterwards, unlike the
other operations. The dividend is shifted left by `p` bits first, which is
what buys the quotient its mantissa.

A divisor of zero divides by zero in ℤ, which is `0` — and bounds nothing,
which is why `SoundFloatArithmetic` asks for a positive one.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def quotDown (a b : Dyadic p) : Dyadic p :=
  ⟨a.mantissa * 2 ^ p / b.mantissa, a.exponent - b.exponent - p⟩

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
