import CORALean.ContSet.ConPolyZono.Float.Operations.AgreeRow
import CORALean.ContSet.ConPolyZono.Real.Operations.AgreeRow

/-!
# An agreement row reads back to the exact layer's

Through `nominal` an index type reads `Fin ((nominal cPZ₁).h + ..)`, which
`Fin.append_left` does not match even though it is the same type; the `rfl`
restatement says so once, at one row.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.toReal_agreeRow (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) (i : Fin n)
    (l : Fin (cPZ₁.h + cPZ₂.h)) :
    toReal (ConPolyZono.agreeRow cPZ₁ cPZ₂ i l)
      = Real.ConPolyZono.agreeRow (nominal cPZ₁) (nominal cPZ₂) i l := by -- --- PROOF ---
  have hreal : Real.ConPolyZono.agreeRow (nominal cPZ₁) (nominal cPZ₂) i
      = (Fin.append (fun l => toReal (cPZ₁.G l i)) fun l => -toReal (cPZ₂.G l i)) := rfl
  rw [hreal]
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l <;>
    simp only [ConPolyZono.agreeRow, Fin.append_left, Fin.append_right, toReal_neg]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
