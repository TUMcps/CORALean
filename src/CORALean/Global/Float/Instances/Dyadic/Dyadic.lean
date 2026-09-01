import CORALean.Global.Float.SoundFloatArithmetic

/-!
# Dyadic numbers at a fixed precision: the representation

`Dyadic p` is `mantissa * 2 ^ exponent` with the mantissa held to `p` bits. The
bound is what makes it a float model: unbounded dyadics are closed under `+`
and `*`, so rounding them would do nothing.

`p` is a phantom parameter rather than a field bound — the class constrains only
`toReal` of a result, so values off the grid are representable but never
produced.

The exponent is unbounded, so nothing overflows. That is exactly what
`SoundFloatArithmetic` assumes, and why this instance needs no axioms where a
binary64 one would.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   18-August-2026
-- Last revision: ---

namespace CORALean.Float

structure Dyadic (p : ℕ) where
  mantissa : ℤ
  exponent : ℤ

noncomputable def Dyadic.toReal {p : ℕ} (d : Dyadic p) : ℝ :=
  (d.mantissa : ℝ) * 2 ^ d.exponent

end CORALean.Float
