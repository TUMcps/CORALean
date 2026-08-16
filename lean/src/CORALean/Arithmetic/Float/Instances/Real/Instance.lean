import CORALean.Arithmetic.Float.SoundFloatArithmetic

/-!
# ℝ as a degenerate instance

Both rounding directions are exact, so this is the class at infinite precision:
the layer collapses to `Arithmetic.Real`, and the class is demonstrably
non-vacuous.

Rounding never widens anything here, so an axiom only floats can violate would
go unnoticed. That is what `Dyadic` is for.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float

-- noncomputable, unlike `Dyadic`: ℝ division is. Nothing computes with it.
noncomputable instance : FloatOps ℝ where
  zero := 0
  neg := Neg.neg
  addUp := (· + ·)
  addDown := (· + ·)
  mulUp := (· * ·)
  mulDown := (· * ·)
  minimum := min
  maximum := max
  half := (· / 2)

noncomputable instance : SoundFloatArithmetic ℝ where
  toReal := id
  toReal_neg _ := rfl
  toReal_zero := rfl
  add_le_addUp _ _ := le_refl _
  addDown_le_add _ _ := le_refl _
  mul_le_mulUp _ _ := le_refl _
  mulDown_le_mul _ _ := le_refl _
  toReal_minimum _ _ := rfl
  toReal_maximum _ _ := rfl
  toReal_half _ := rfl

end CORALean.Arithmetic.Float
