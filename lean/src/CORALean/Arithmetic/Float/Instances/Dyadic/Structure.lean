import CORALean.Arithmetic.Float.SoundFloatArithmetic

/-!
# Dyadic numbers at a fixed precision: the representation

`Dyadic p` is `mantissa * 2 ^ exponent` with the mantissa held to `p` bits, and
`toReal` is the number it stands for. The bound is what makes it a float model:
unbounded dyadics are closed under `+` and `*`, so rounding them would do
nothing and the instance would be as degenerate as ℝ.

Precision is a phantom parameter, not a field bound: the class constrains only
`toReal` of a result, so carrying a proof would prove nothing extra. Values off
the grid are representable but never produced.

The exponent is unbounded, so nothing overflows — exactly what
`SoundFloatArithmetic` assumes, and why this instance needs no axioms where a
binary64 one would.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   18-August-2026
-- Last revision: ---

namespace CORALean.Arithmetic.Float

structure Dyadic (p : ℕ) where
  mantissa : ℤ
  exponent : ℤ

noncomputable def Dyadic.toReal {p : ℕ} (d : Dyadic p) : ℝ :=
  (d.mantissa : ℝ) * 2 ^ d.exponent

end CORALean.Arithmetic.Float
