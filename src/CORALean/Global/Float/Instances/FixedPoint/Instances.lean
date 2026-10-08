import CORALean.Global.Float.ToRat
import CORALean.Global.Float.Instances.FixedPoint.Operations.API
import CORALean.Global.Float.Instances.FixedPoint.Theorems.DivDownLeDiv
import CORALean.Global.Float.Instances.FixedPoint.Theorems.LeDivUp
import CORALean.Global.Float.Instances.FixedPoint.Theorems.LeRoundUp
import CORALean.Global.Float.Instances.FixedPoint.Theorems.RoundDownLe
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealExactAdd
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealExactMul
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealHalf
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealLeOfLe
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealMaximum
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealMinimum
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealMkZero
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealNeg

/-!
# `FixedPoint` as a sound float model

Each obligation is exactness composed with a rounding direction, the two
halves proved separately in `Theorems`. Division has no exact half to compose
with and arrives already directed. `le` is exact and needs no rounding at all.
No bound on the mantissa is needed: leaving `f` digits costs precision, never
soundness.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  INSTANCES  ========================================= --

instance {f : ℕ} : FloatOps (FixedPoint f) where
  zero := ⟨0, 0⟩
  one := ⟨1, 0⟩
  neg := FixedPoint.neg
  addUp := FixedPoint.addUp
  addDown := FixedPoint.addDown
  mulUp := FixedPoint.mulUp
  mulDown := FixedPoint.mulDown
  divUp := FixedPoint.divUp
  divDown := FixedPoint.divDown
  minimum := FixedPoint.minimum
  maximum := FixedPoint.maximum
  le := FixedPoint.le
  half := FixedPoint.half

/-- Computable, which is what lets an algorithm written against the operation
classes be *run* at `FixedPoint`: a `toReal` the compiler cannot erase would
make every instance derived from this one noncomputable. -/
instance {f : ℕ} : SoundFloatArithmetic (FixedPoint f) where
  toReal := FixedPoint.toReal
  toReal_neg := FixedPoint.toReal_neg
  toReal_zero := FixedPoint.toReal_mk_zero 0
  toReal_one := by
    show FixedPoint.toReal (⟨1, 0⟩ : FixedPoint f) = 1
    rw [FixedPoint.toReal_def]
    norm_num
  add_le_addUp a b := FixedPoint.toReal_exactAdd a b ▸ FixedPoint.le_roundUp _
  addDown_le_add a b := FixedPoint.toReal_exactAdd a b ▸ FixedPoint.roundDown_le _
  mul_le_mulUp a b := FixedPoint.toReal_exactMul a b ▸ FixedPoint.le_roundUp _
  mulDown_le_mul a b := FixedPoint.toReal_exactMul a b ▸ FixedPoint.roundDown_le _
  div_le_divUp := FixedPoint.le_divUp
  divDown_le_div := FixedPoint.divDown_le_div
  toReal_minimum := FixedPoint.toReal_minimum
  toReal_maximum := FixedPoint.toReal_maximum
  toReal_le_of_le := FixedPoint.toReal_le_of_le
  toReal_half := FixedPoint.toReal_half

/-- `m / 10 ^ d`, the rational `toReal` already casts. -/
instance {f : ℕ} : ToRat (FixedPoint f) where
  toRat x := (x.m : ℚ) / 10 ^ x.d
  toReal_toRat _ := rfl
  isNaN _ := false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
