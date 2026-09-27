import CORALean.Global.Float.Instances.Dyadic.API

/-!
# Round-to-nearest at `p` bits, WITHOUT guarantees

`NearestFloat` at a precision the machine does not offer: binary32 is `p = 24`,
and the smaller formats below it. The representation is `Dyadic p`'s, and so are
the exact sum and product; what differs is the rounding back to `p` bits, which
here is to nearest with ties to even, as IEEE 754 rounds by default, in both
directions alike. The exponent stays unbounded, so there are no subnormals and
nothing overflows: this models a format's precision, not its range.

The quotient is not dyadic, so it is rounded while the integers are still there,
as `Dyadic.quotDown` does: `p + 1` bits at least, one more for the halfway bit,
and a sticky bit for whether anything was left over. That is enough to round
correctly, and it is what `NearestFloat` at `p = 53` is checked against.

Nothing here is sound: the six false laws are fields of `NearestUnsound`,
assumed in `Axioms`, and at `Dyadic` they are refutable, not merely unprovable.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- A `Dyadic p` computed with round-to-nearest in both directions. Unsound: a
bench baseline only. -/
structure NearestDyadic (p : ℕ) where
  val : Dyadic p

namespace NearestDyadic

variable {p : ℕ}

/-- The number it denotes, exactly as for `Dyadic p`. -/
def toReal (a : NearestDyadic p) : ℝ := a.val.toReal

/-- `d` to `p` significand bits, to nearest with ties to even: the magnitude's
dropped bits against half a unit, the sign restored afterwards. Zero at exponent `0`,
as IEEE's zero has none: carried along, its exponent would drift with every product. -/
def roundNearest (d : Dyadic p) : Dyadic p :=
  if d.mantissa = 0 then ⟨0, 0⟩ else
  let s := d.shift                                          -- the bits beyond `p`
  let m := d.mantissa.natAbs
  let q := m / 2 ^ s                                        -- truncated towards zero
  let r := m % 2 ^ s                                        -- what truncation dropped
  let up := decide (2 ^ s < 2 * r) || (2 * r == 2 ^ s && q % 2 == 1)  -- past half, or odd tie
  let q' : ℤ := if up then q + 1 else q
  ⟨if d.mantissa < 0 then -q' else q', d.exponent + s⟩

/-- `a / b` to nearest: at least `p + 1` quotient bits as `Dyadic.quotDown` takes,
one more for the halfway bit, and a sticky bit for a nonzero remainder. -/
def quotNearest (a b : Dyadic p) : Dyadic p :=
  let k := p + b.mantissa.natAbs.log2 + 1                   -- as `Dyadic.quotDown`
  let num := a.mantissa.natAbs * 2 ^ k
  let den := b.mantissa.natAbs
  let m : ℤ := 2 * (num / den) + (if num % den == 0 then 0 else 1)  -- halfway bit, sticky bit
  let neg := decide (a.mantissa < 0) != decide (b.mantissa < 0)
  roundNearest ⟨if neg then -m else m, a.exponent - b.exponent - k - 1⟩

/-- The exact sum, rounded to nearest; used as `addUp` and `addDown` both. -/
def add (a b : NearestDyadic p) : NearestDyadic p := ⟨roundNearest (a.val.exactAdd b.val)⟩

/-- The exact product, rounded to nearest; used as `mulUp` and `mulDown` both. -/
def mul (a b : NearestDyadic p) : NearestDyadic p := ⟨roundNearest (a.val.exactMul b.val)⟩

/-- The quotient, rounded to nearest; used as `divUp` and `divDown` both. -/
def div (a b : NearestDyadic p) : NearestDyadic p := ⟨quotNearest a.val b.val⟩

end NearestDyadic

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
