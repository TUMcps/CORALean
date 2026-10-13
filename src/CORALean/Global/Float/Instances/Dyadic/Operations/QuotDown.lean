module

public import CORALean.Global.Float.Instances.Dyadic.Dyadic

@[expose] public section

/-!
# The quotient, rounded down while dividing

A quotient of dyadics is a general rational, so the direction has to be
chosen while the integers are still there rather than afterwards, unlike the
other operations. The dividend is shifted left first, by `p` bits plus the
divisor's own length, which is what buys the quotient its `p`-bit mantissa
whatever the dividend's: a shift of `p` alone leaves `1 / k!` one bit once `k!`
fills `p` bits of its own.

A divisor of zero divides by zero in ℤ, which is `0` — and bounds nothing,
which is why `SoundFloatArithmetic` asks for a positive one.
-/

-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   25-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def quotDown (a b : Dyadic p) : Dyadic p :=
  ⟨a.mantissa * 2 ^ (p + b.mantissa.natAbs.log2 + 1) / b.mantissa,
    a.exponent - b.exponent - ((p + b.mantissa.natAbs.log2 + 1 : ℕ) : ℤ)⟩

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
