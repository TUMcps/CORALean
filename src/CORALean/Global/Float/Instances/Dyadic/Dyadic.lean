module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# Dyadic numbers at a fixed precision: the representation

`Dyadic p` is `mantissa * 2 ^ exponent` with the mantissa held to `p` bits. `p` is a phantom
parameter rather than a field bound, since the class constrains only `toReal` of a result, so values
off the grid are representable but never produced. The exponent is unbounded, so nothing overflows,
which is what `SoundFloatArithmetic` assumes and why this instance needs no axioms. `toReal` takes
its power of two through ℚ, which makes the scalar *runnable*: ℝ's inversion is noncomputable and
ℚ's is not, and a class field of type `𝕋 → ℝ` is data the compiler cannot erase, so a noncomputable
`toReal` would make every generic algorithm at this type noncomputable. `toReal_def` is the number
it denotes.

## References

None: a CORALean scalar type, defined here to make the library runnable; CORA has no such class.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- A dyadic number `mantissa · 2 ^ exponent`; the precision `p` is a phantom parameter. -/
structure Dyadic (p : ℕ) where
  mantissa : ℤ
  exponent : ℤ

/-- The real number a dyadic denotes. -/
def Dyadic.toReal {p : ℕ} (d : Dyadic p) : ℝ :=
  (d.mantissa : ℝ) * ((2 ^ d.exponent : ℚ) : ℝ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
