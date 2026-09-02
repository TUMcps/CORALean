import CORALean.Global.Float.Instances.Dyadic.Theorems.Order
import CORALean.Global.Float.Instances.Dyadic.Theorems.Rounding

/-!
# `Dyadic` as a sound float model

Each obligation is exactness composed with a rounding direction, the two halves
proved separately in `Theorems`. No bound on the mantissa is needed: leaving the
grid costs precision, never soundness.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

instance {p : ℕ} : FloatOps (Dyadic p) where
  zero := ⟨0, 0⟩
  one := ⟨1, 0⟩
  neg := Dyadic.neg
  addUp := Dyadic.addUp
  addDown := Dyadic.addDown
  mulUp := Dyadic.mulUp
  mulDown := Dyadic.mulDown
  minimum := Dyadic.minimum
  maximum := Dyadic.maximum
  le := Dyadic.le
  half := Dyadic.half

noncomputable instance {p : ℕ} : SoundFloatArithmetic (Dyadic p) where
  toReal := Dyadic.toReal
  toReal_neg := Dyadic.toReal_neg
  toReal_zero := Dyadic.toReal_mk_zero 0
  toReal_one := by show ((1:ℤ) : ℝ) * 2 ^ (0:ℤ) = 1; norm_num
  add_le_addUp a b := Dyadic.toReal_exactAdd a b ▸ Dyadic.le_roundUp _
  addDown_le_add a b := Dyadic.toReal_exactAdd a b ▸ Dyadic.roundDown_le _
  mul_le_mulUp a b := Dyadic.toReal_exactMul a b ▸ Dyadic.le_roundUp _
  mulDown_le_mul a b := Dyadic.toReal_exactMul a b ▸ Dyadic.roundDown_le _
  toReal_minimum := Dyadic.toReal_minimum
  toReal_maximum := Dyadic.toReal_maximum
  toReal_half := Dyadic.toReal_half

end CORALean.Float
