import CORALean.Examples.Bench.NearestUnsound.Axioms

/-!
# The round-to-nearest scalars as float models, UNSOUNDLY

`FloatOps` with one operation in both directions, and `SoundFloatArithmetic`
whose six rounding laws are projections of `nearestUnsound`, the false axiom in
`Axioms`, as `Float`'s are of `Binary64.trustedHardware`. Every other law is
true of round-to-nearest and proved: at `NearestFloat` from `trustedHardware`,
as native `Float` proves it, and at `NearestDyadic` from `Dyadic`'s own lemmas.
Every data field is an ordinary computable definition, so the library's
algorithms compile and run here unchanged.

`scoped`, in `CORALean.Bench.NearestUnsound`, the false property's own namespace:
nothing sees these instances unless it opens that namespace, which only the
bench's `--type nearest` branch does. A result obtained through them carries no
guarantee whatsoever.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench.NearestUnsound

open CORALean.Float


-- ========================================  INSTANCES  ========================================= --

/-- The machine's round-to-nearest operations, one per pair of directions. -/
scoped instance : FloatOps NearestFloat where
  zero := ⟨0.0⟩
  one := ⟨1.0⟩
  neg a := ⟨-a.val⟩
  addUp := NearestFloat.add
  addDown := NearestFloat.add
  mulUp := NearestFloat.mul
  mulDown := NearestFloat.mul
  divUp := NearestFloat.div
  divDown := NearestFloat.div
  minimum a b := ⟨min a.val b.val⟩
  maximum a b := ⟨max a.val b.val⟩
  le a b := decide (a.val ≤ b.val)
  half a := ⟨Binary64.half a.val⟩

/-- The six rounding laws from the false `nearestUnsound`; the rest are `Float`'s own. -/
scoped instance : SoundFloatArithmetic NearestFloat where
  toReal := NearestFloat.toReal
  toReal_neg a := Binary64.trustedHardware.toReal_neg a.val
  toReal_zero := Binary64.trustedHardware.toReal_zero
  toReal_one := Binary64.trustedHardware.toReal_one
  add_le_addUp := nearestUnsound.float_add_le_addUp
  addDown_le_add := nearestUnsound.float_addDown_le_add
  mul_le_mulUp := nearestUnsound.float_mul_le_mulUp
  mulDown_le_mul := nearestUnsound.float_mulDown_le_mul
  div_le_divUp := nearestUnsound.float_div_le_divUp
  divDown_le_div := nearestUnsound.float_divDown_le_div
  toReal_minimum a b := Binary64.trustedHardware.toReal_min a.val b.val
  toReal_maximum a b := Binary64.trustedHardware.toReal_max a.val b.val
  toReal_le_of_le h := Binary64.trustedHardware.toReal_le_of_le _ _ (of_decide_eq_true h)
  toReal_half a := Binary64.trustedHardware.toReal_half a.val

/-- Round-to-nearest-even at `p` bits, one per pair of directions. -/
scoped instance {p : ℕ} : FloatOps (NearestDyadic p) where
  zero := ⟨⟨0, 0⟩⟩
  one := ⟨⟨1, 0⟩⟩
  neg a := ⟨a.val.neg⟩
  addUp := NearestDyadic.add
  addDown := NearestDyadic.add
  mulUp := NearestDyadic.mul
  mulDown := NearestDyadic.mul
  divUp := NearestDyadic.div
  divDown := NearestDyadic.div
  minimum a b := ⟨a.val.minimum b.val⟩
  maximum a b := ⟨a.val.maximum b.val⟩
  le a b := a.val.le b.val
  half a := ⟨a.val.half⟩

/-- The six rounding laws from the false `nearestUnsound`; the rest are `Dyadic`'s own. -/
scoped instance {p : ℕ} : SoundFloatArithmetic (NearestDyadic p) where
  toReal := NearestDyadic.toReal
  toReal_neg a := Dyadic.toReal_neg a.val
  toReal_zero := Dyadic.toReal_mk_zero 0
  toReal_one := by
    show Dyadic.toReal (⟨1, 0⟩ : Dyadic p) = 1
    rw [Dyadic.toReal_def]
    norm_num
  add_le_addUp := nearestUnsound.dyadic_add_le_addUp
  addDown_le_add := nearestUnsound.dyadic_addDown_le_add
  mul_le_mulUp := nearestUnsound.dyadic_mul_le_mulUp
  mulDown_le_mul := nearestUnsound.dyadic_mulDown_le_mul
  div_le_divUp := nearestUnsound.dyadic_div_le_divUp
  divDown_le_div := nearestUnsound.dyadic_divDown_le_div
  toReal_minimum a b := Dyadic.toReal_minimum a.val b.val
  toReal_maximum a b := Dyadic.toReal_maximum a.val b.val
  toReal_le_of_le h := Dyadic.toReal_le_of_le h
  toReal_half a := Dyadic.toReal_half a.val

end CORALean.Bench.NearestUnsound


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
