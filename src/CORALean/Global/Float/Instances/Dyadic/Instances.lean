module

public import CORALean.Global.Float.Instances.Dyadic.Theorems.AddDownLeAdd
public import CORALean.Global.Float.Instances.Dyadic.Theorems.AddLeAddUp
public import CORALean.Global.Float.Instances.Dyadic.Theorems.Basic
public import CORALean.Global.Float.ToRat
public import CORALean.Global.Float.Instances.Dyadic.Operations.Basic
public import CORALean.Global.Float.Instances.Dyadic.Theorems.DivDownLeDiv
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeDivUp
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeRoundUp
public import CORALean.Global.Float.Instances.Dyadic.Theorems.RoundDownLe
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactMul
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMaximum
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMinimum

@[expose] public section

/-!
# `Dyadic` as a sound float model

Each obligation is exactness composed with a rounding direction, the two halves
proved separately in `Theorems`. Division has no exact half to compose with and
arrives already directed. `le` is exact and needs no rounding at all. No bound
on the mantissa is needed: leaving the grid costs precision, never soundness.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  INSTANCES  ========================================= --

instance {p : ℕ} : FloatOps (Dyadic p) where
  zero := ⟨0, 0⟩
  one := ⟨1, 0⟩
  neg := Dyadic.neg
  addUp := Dyadic.addUp
  addDown := Dyadic.addDown
  mulUp := Dyadic.mulUp
  mulDown := Dyadic.mulDown
  divUp := Dyadic.divUp
  divDown := Dyadic.divDown
  minimum := Dyadic.minimum
  maximum := Dyadic.maximum
  le := Dyadic.le
  half := Dyadic.half

/-- Computable, which is what lets an algorithm written against the operation
classes be *run* at `Dyadic`: a `toReal` the compiler cannot erase would make
every instance derived from this one noncomputable. -/
instance {p : ℕ} : SoundFloatArithmetic (Dyadic p) where
  toReal := Dyadic.toReal
  toReal_neg := Dyadic.toReal_neg
  toReal_zero := Dyadic.toReal_mk_zero 0
  toReal_one := by
    show Dyadic.toReal (⟨1, 0⟩ : Dyadic p) = 1
    rw [Dyadic.toReal_def]
    norm_num
  add_le_addUp := Dyadic.add_le_addUp
  addDown_le_add := Dyadic.addDown_le_add
  mul_le_mulUp a b := Dyadic.toReal_exactMul a b ▸ Dyadic.le_roundUp _
  mulDown_le_mul a b := Dyadic.toReal_exactMul a b ▸ Dyadic.roundDown_le _
  div_le_divUp := Dyadic.le_divUp
  divDown_le_div := Dyadic.divDown_le_div
  toReal_minimum := Dyadic.toReal_minimum
  toReal_maximum := Dyadic.toReal_maximum
  toReal_le_of_le := Dyadic.toReal_le_of_le
  toReal_half := Dyadic.toReal_half

/-- `m · 2 ^ e` in ℚ, exact. -/
instance {p : ℕ} : ToRat (Dyadic p) where
  toRat := Dyadic.toRat
  toReal_toRat := Dyadic.cast_toRat
  isNaN _ := false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
