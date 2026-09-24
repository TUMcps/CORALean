import CORALean.Global.Float.SoundFloatArithmetic

/-!
# ℝ as a degenerate instance

Both rounding directions are exact, so this is the class at infinite precision
and the float layer collapses to `Real`. Rounding never widens anything here, so
an axiom only floats can violate would go unnoticed — that is what `Dyadic` is
for.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  INSTANCES  ========================================= --

-- noncomputable, unlike `Dyadic`: ℝ division is. Nothing computes with it.
noncomputable instance : FloatOps ℝ where
  zero := 0
  one := 1
  neg := Neg.neg
  addUp := (· + ·)
  addDown := (· + ·)
  mulUp := (· * ·)
  mulDown := (· * ·)
  divUp := (· / ·)
  divDown := (· / ·)
  minimum := min
  maximum := max
  le := fun a b => decide (a ≤ b)
  half := (· / 2)

-- every field is `rfl` or `le_refl`: at ℝ each rounding is the exact operation
noncomputable instance : SoundFloatArithmetic ℝ where
  toReal x := x
  toReal_neg _ := rfl
  toReal_zero := rfl
  toReal_one := rfl
  add_le_addUp _ _ := le_refl _
  addDown_le_add _ _ := le_refl _
  mul_le_mulUp _ _ := le_refl _
  mulDown_le_mul _ _ := le_refl _
  div_le_divUp _ _ _ := le_refl _
  divDown_le_div _ _ _ := le_refl _
  toReal_minimum _ _ := rfl
  toReal_maximum _ _ := rfl
  toReal_le_of_le h := of_decide_eq_true h
  toReal_half _ := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
