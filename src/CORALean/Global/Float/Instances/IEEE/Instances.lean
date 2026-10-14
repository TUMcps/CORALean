module

public import CORALean.Global.Float.Instances.Dyadic.Theorems.Basic
public import CORALean.Global.Float.ToRat
public import CORALean.Global.Float.Instances.IEEE.Theorems.Basic
public import CORALean.Global.Float.Instances.IEEE.Theorems.ToRealMaximum
public import CORALean.Global.Float.Instances.IEEE.Theorems.ToRealMinimum

@[expose] public section

/-!
# `IEEE fmt` as a sound float model

Every obligation is a theorem in `Theorems`, so this instance rests on Lean's own axioms alone,
as `Dyadic`'s does and `Float`'s does not. `zero` and `one` are numbers of every format here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  INSTANCES  ========================================= --

instance {fmt : IEEEFormat} : FloatOps (IEEE fmt) where
  zero := ⟨0, 0⟩
  one := ⟨1, 0⟩
  neg := IEEE.neg
  addUp := IEEE.addUp
  addDown := IEEE.addDown
  mulUp := IEEE.mulUp
  mulDown := IEEE.mulDown
  divUp := IEEE.divUp
  divDown := IEEE.divDown
  minimum := IEEE.minimum
  maximum := IEEE.maximum
  le := IEEE.le
  half := IEEE.half

/-- Computable, like `Dyadic`'s, so an algorithm runs at every format. -/
instance {fmt : IEEEFormat} : SoundFloatArithmetic (IEEE fmt) where
  toReal := IEEE.toReal
  toReal_neg := IEEE.toReal_neg
  toReal_zero := Dyadic.toReal_mk_zero 0
  toReal_one := by
    show Dyadic.toReal (⟨1, 0⟩ : Dyadic fmt.p) = 1
    rw [Dyadic.toReal_def]
    norm_num
  add_le_addUp := IEEE.add_le_addUp
  addDown_le_add := IEEE.addDown_le_add
  mul_le_mulUp := IEEE.mul_le_mulUp
  mulDown_le_mul := IEEE.mulDown_le_mul
  div_le_divUp := IEEE.div_le_divUp
  divDown_le_div := IEEE.divDown_le_div
  toReal_minimum := IEEE.toReal_minimum
  toReal_maximum := IEEE.toReal_maximum
  toReal_le_of_le h := (IEEE.le_iff _ _).mp h
  toReal_half := IEEE.toReal_half

/-- The stored dyadic, decoded exactly. -/
instance {fmt : IEEEFormat} : ToRat (IEEE fmt) where
  toRat x := x.toDyadic.toRat
  toReal_toRat x := Dyadic.cast_toRat x.toDyadic
  isNaN _ := false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
