import CORALean.Arithmetic.Float.SoundFloatArithmetic

/-!
# ℝ as a degenerate instance

Both rounding directions are exact, so this is the class at infinite precision
and `Arithmetic.Real` is what the layer collapses to. It keeps the class
demonstrably non-vacuous.

It cannot do the other job an instance has, though: because rounding never
widens anything here, an axiom that only floats violate would go unnoticed. That
is what `Dyadic` is for.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float

instance : FloatOps ℝ where
  zero := 0
  neg := Neg.neg
  addUp := (· + ·)
  addDown := (· + ·)
  mulUp := (· * ·)
  mulDown := (· * ·)

instance : SoundFloatArithmetic ℝ where
  toReal := id
  toReal_neg _ := rfl
  toReal_zero := rfl
  add_le_addUp _ _ := le_refl _
  addDown_le_add _ _ := le_refl _
  mul_le_mulUp _ _ := le_refl _
  mulDown_le_mul _ _ := le_refl _

end CORALean.Arithmetic.Float
