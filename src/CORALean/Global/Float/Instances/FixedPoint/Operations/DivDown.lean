import CORALean.Global.Float.Instances.FixedPoint.FixedPoint

/-!
# Division, rounded down

Unlike addition and multiplication, a quotient of fixed-point values is not
one, so there is no exact step to round afterwards: `a.m / 10 ^ a.d` over
`b.m / 10 ^ b.d` is `a.m · 10 ^ b.d` over `b.m · 10 ^ a.d`, and this floors
that exact rational straight to `f` digits in one division, `/` on ℤ being
floor division.

A divisor of zero divides by zero in ℤ, which is `0` -- and bounds nothing,
which is why `SoundFloatArithmetic` asks for a positive one; a negative
divisor floors the wrong way, which is why it asks for exactly that.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace FixedPoint

variable {f : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def divDown (a b : FixedPoint f) : FixedPoint f := ⟨(a.m * 10 ^ (b.d + f)) / (10 ^ a.d * b.m), f⟩

end FixedPoint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
