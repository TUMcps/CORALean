import CORALean.Global.Float.Instances.Dyadic.Dyadic

/-!
# Native binary64: what a `Float` denotes

Lean's `Float` is IEEE 754 binary64 compiled to a machine double, and opaque in
the logic: nothing about `Float.add` is provable, which is why the obligations
`SoundFloatArithmetic` states are assumed in `Axioms` rather than proved.

The real interpretation is not assumed. A finite binary64 is `m · 2 ^ e` with
both integers read off the 64 bits, so `toReal` is a *definition* here exactly
as it is at `Dyadic`, and it is `Dyadic 53`'s — the significand carries 53 bits
once the implicit leading one is counted.

The decoding is the standard one: sign bit, an 11-bit exponent field biased by
1023, and 52 stored significand bits whose leading one is implicit unless that
field is zero. The same formula is applied when the field is `0x7FF`, where the
bit pattern is an infinity or a NaN and the dyadic it returns (`2 ^ 1024`, `1.5 * 2 ^ 1024`) is no
value of the machine;
`Axioms` is where that costs something.
-/

-- Authors:       Claude Opus 5
-- Written:       22-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64

/-- `-1` when the sign bit is set, `1` otherwise — including at `-0.0`, whose
significand is zero and whose sign therefore costs nothing. -/
def sign (x : Float) : ℤ := if x.toBits >>> 63 == 1 then -1 else 1

/-- The 11 exponent bits, still biased. `0` selects the subnormal branch. -/
def expField (x : Float) : ℕ := ((x.toBits >>> 52) &&& 0x7FF).toNat

/-- The 52 stored significand bits, without the implicit leading one. -/
def sigField (x : Float) : ℤ := ((x.toBits &&& 0xFFFFFFFFFFFFF).toNat : ℤ)

/-- The number the bits denote, as `m · 2 ^ e`. The bias is 1023 and the
significand is scaled by `2 ^ 52`, so an ordinary exponent field `E` denotes
`E - 1023 - 52`, and the subnormal branch denotes the same at `E = 1`. -/
def toDyadic (x : Float) : Dyadic 53 :=
  if expField x == 0 then ⟨sign x * sigField x, -1074⟩
  else ⟨sign x * (sigField x + 2 ^ 52), (expField x : ℤ) - 1075⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Computable, which is what lets an algorithm be *run* at `Float`: the class
field is data, and `Dyadic.toReal` takes its power of two through ℚ so that it
computes, which this inherits. -/
def toReal (x : Float) : ℝ := (toDyadic x).toReal

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
