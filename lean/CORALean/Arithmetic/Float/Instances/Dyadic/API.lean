import CORALean.Arithmetic.Float.SoundFloatArithmetic

/-!
# Dyadic numbers at a fixed precision

`Dyadic p` is `mantissa * 2 ^ exponent` with the mantissa held to `p` bits. The
bound is what makes it a float model: unbounded dyadics are closed under `+` and
`*`, so rounding them would do nothing and the instance would be as degenerate
as ℝ.

Every operation is exact-then-round. The exact step may overflow `p` bits — a
product needs `2p` — so it is separate, and `roundUp`/`roundDown` return to the
grid by shifting the mantissa right, taking the floor or the ceiling.

Precision is a phantom parameter, not a field bound: the class constrains only
`toReal` of a result, so carrying a proof would prove nothing extra. Values off
the grid are representable but never produced.

The exponent is unbounded, so nothing overflows — exactly what
`SoundFloatArithmetic` assumes, and why this instance needs no axioms where a
binary64 one would.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float

structure Dyadic (p : ℕ) where
  mantissa : ℤ
  exponent : ℤ

namespace Dyadic

variable {p : ℕ}

noncomputable def toReal (d : Dyadic p) : ℝ := (d.mantissa : ℝ) * 2 ^ d.exponent

def neg (d : Dyadic p) : Dyadic p := ⟨-d.mantissa, d.exponent⟩

/-! ## The exact step

Closed on dyadics, so these lose nothing; only the mantissa grows. -/

/-- Aligned to the smaller exponent, where both mantissas are integers. -/
def exactAdd (a b : Dyadic p) : Dyadic p :=
  let e := min a.exponent b.exponent
  ⟨a.mantissa * 2 ^ (a.exponent - e).toNat + b.mantissa * 2 ^ (b.exponent - e).toNat, e⟩

def exactMul (a b : Dyadic p) : Dyadic p :=
  ⟨a.mantissa * b.mantissa, a.exponent + b.exponent⟩

/-! ## The rounding step

`shift` is how far the mantissa exceeds `p` bits. Integer `/` is floor division
on ℤ, and the ceiling is the floor of the negation. -/

def shift (d : Dyadic p) : ℕ := Nat.log2 d.mantissa.natAbs + 1 - p

def roundDown (d : Dyadic p) : Dyadic p :=
  ⟨d.mantissa / 2 ^ d.shift, d.exponent + d.shift⟩

def roundUp (d : Dyadic p) : Dyadic p :=
  ⟨-(-d.mantissa / 2 ^ d.shift), d.exponent + d.shift⟩

/-! ## Comparison

Exact, and needing no rounding: aligned to the common exponent, the order on
dyadics is the order on their mantissas. -/

def le (a b : Dyadic p) : Bool :=
  a.mantissa * 2 ^ (a.exponent - min a.exponent b.exponent).toNat ≤
    b.mantissa * 2 ^ (b.exponent - min a.exponent b.exponent).toNat

/-- Exact: the mantissa is untouched. -/
def half (a : Dyadic p) : Dyadic p := ⟨a.mantissa, a.exponent - 1⟩

def minimum (a b : Dyadic p) : Dyadic p := if le a b then a else b
def maximum (a b : Dyadic p) : Dyadic p := if le a b then b else a

/-! ## Rounded arithmetic -/

def addUp (a b : Dyadic p) : Dyadic p := roundUp (exactAdd a b)
def addDown (a b : Dyadic p) : Dyadic p := roundDown (exactAdd a b)
def mulUp (a b : Dyadic p) : Dyadic p := roundUp (exactMul a b)
def mulDown (a b : Dyadic p) : Dyadic p := roundDown (exactMul a b)

end Dyadic

end CORALean.Arithmetic.Float
