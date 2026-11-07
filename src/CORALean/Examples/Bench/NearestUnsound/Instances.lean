import CORALean.Examples.Bench.NearestUnsound.Axioms
import CORALean.Examples.Bench.NearestUnsound.NearestDyadic
import CORALean.Examples.Bench.NearestUnsound.NearestFloat
import CORALean.Examples.Bench.NearestUnsound.NearestUnsound
import CORALean.Global.Float.Instances.Binary64.Definitions.Axioms
import CORALean.Global.Float.Instances.Dyadic.Theorems.Basic
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDef
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMaximum
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMinimum
import CORALean.Global.Float.Interfaces
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# The round-to-nearest scalars as float models, UNSOUNDLY

`FloatOps` with one operation in both directions, and `SoundFloatArithmetic` whose six rounding
laws are projections of `nearestUnsound`, the false axiom in `Axioms`, as `Float`'s are of
`Binary64.trustedHardware`. Every other law is true of round-to-nearest and proved: at
`NearestFloat` from `trustedHardware`, at `NearestDyadic` from `Dyadic`'s own lemmas. Every data
field is an ordinary computable definition, so the library's algorithms run here unchanged. The
instances are `scoped` in `CORALean.Bench.NearestUnsound`, which only the bench's `--type nearest`
branch opens; a result obtained through them carries no guarantee whatsoever.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   07-November-2026
-- Reviewed:      ---


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
  minimum a b := ⟨Binary64.minimum a.val b.val⟩
  maximum a b := ⟨Binary64.maximum a.val b.val⟩
  le a b := decide (a.val ≤ b.val)
  half a := ⟨Binary64.half a.val⟩
  -- the machine's `<`: at round-to-nearest `a + 2⁻⁶⁴` rounds back to `a`, no strict test
  ltStrict a b := decide (a.val < b.val)
  -- the machine's correctly rounded `sqrt`; the issue-274 witness is Newton stopping 1 ulp short
  sqrtUpOverride := some NearestFloat.sqrt

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
  toReal_lt_of_ltStrict h := nearestUnsound.float_lt_of_lt _ _ (of_decide_eq_true h)
  le_sqrtUpOverride hf p a := by
    cases hf
    exact nearestUnsound.float_le_sqrt p a

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
  -- `a ≤ b` and not `b ≤ a`: here too `a + 2⁻⁶⁴` rounds back to `a`
  ltStrict a b := a.val.le b.val && !b.val.le a.val

/-- The six rounding laws from the false `nearestUnsound`; the rest are `Dyadic`'s own. -/
scoped instance {p : ℕ} : SoundFloatArithmetic (NearestDyadic p) where
  -- the reading, then the sign and rounding laws, then the order and halving ones
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
  -- strict: `a ≤ b` and not `b ≤ a`, read as reals
  toReal_lt_of_ltStrict {a b} h := by
    obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
    exact lt_of_le_not_ge (Dyadic.toReal_le_of_le h₁)
      fun h₃ => by simp [(Dyadic.le_iff b.val a.val).mpr h₃] at h₂
  le_sqrtUpOverride hf := by cases hf

/-- The bits, decoded exactly, as for `Float`: no `nearestUnsound` involved. -/
scoped instance : ToRat NearestFloat where
  toRat a := (Binary64.toDyadic a.val).toRat
  toReal_toRat a := Dyadic.cast_toRat (Binary64.toDyadic a.val)
  isNaN a := a.val.isNaN

/-- The stored dyadic, decoded exactly. -/
scoped instance {p : ℕ} : ToRat (NearestDyadic p) where
  toRat a := a.val.toRat
  toReal_toRat a := Dyadic.cast_toRat a.val
  isNaN _ := false

end CORALean.Bench.NearestUnsound


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
