import CORALean.ContSet.ConPolyZono.Float.Operations.AgreeRow
import CORALean.ContSet.ConPolyZono.Real.Operations.AgreeRow

/-!
# An agreement row reads back to the exact layer's

Through `nominal` an index type reads `Fin ((nominal C₁).h + ..)`, which
`Fin.append_left` does not match even though it is the same type; the `rfl`
restatement says so once, at one row.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem ConPolyZono.toReal_agreeRow (C₁ C₂ : ConPolyZono 𝕋 n) (i : Fin n)
    (l : Fin (C₁.h + C₂.h)) :
    toReal (ConPolyZono.agreeRow C₁ C₂ i l)
      = Real.ConPolyZono.agreeRow (nominal C₁) (nominal C₂) i l := by
  have hreal : Real.ConPolyZono.agreeRow (nominal C₁) (nominal C₂) i
      = (Fin.append (fun l => toReal (C₁.G i l)) fun l => -toReal (C₂.G i l)) := rfl
  rw [hreal]
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l <;>
    simp only [ConPolyZono.agreeRow, Fin.append_left, Fin.append_right, toReal_neg]

end CORALean.Float
