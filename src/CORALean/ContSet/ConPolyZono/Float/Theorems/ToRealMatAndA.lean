import CORALean.ContSet.ConPolyZono.Float.Operations.AndA
import CORALean.ContSet.ConPolyZono.Real.Operations.AndA
import CORALean.ContSet.ConPolyZono.Float.Operations.AgreeRow
import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealAgreeRow
import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatPlusA

/-!
# The constraint matrix `andA` reads back to the exact layer's

Field by field: the `plus` block is the exact layer's `plusA` of the two
read-back matrices, and the agreement block is `toReal_agreeRow` read one row
at a time.
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

theorem ConPolyZono.toRealMat_andA (C₁ C₂ : ConPolyZono 𝕋 n) :
    toRealMat (ConPolyZono.andA C₁ C₂)
      = Real.ConPolyZono.andA (nominal C₁) (nominal C₂) := by -- --- PROOF ---
  -- the exact layer's matrix spelled out, so the four `Fin.addCases` branches below match it
  have hreal : Real.ConPolyZono.andA (nominal C₁) (nominal C₂)
      = fun i => Fin.append
          (fun r => Fin.append (Real.ConPolyZono.plusA (toRealMat C₁.A) (toRealMat C₂.A) r)
            (0 : Fin (C₁.h + C₂.h) → ℝ))
          (fun r => Fin.append (0 : Fin (C₁.s + C₂.s) → ℝ)
            (Real.ConPolyZono.agreeRow (nominal C₁) (nominal C₂) r)) i := rfl
  rw [hreal]
  refine funext (Fin.addCases (fun i => ?_) fun i => ?_) <;>
    refine funext (Fin.addCases (fun l => ?_) fun l => ?_)
  · simp only [toRealMat, ConPolyZono.andA, Fin.append_left]
    exact congrFun (congrFun (ConPolyZono.toRealMat_plusA C₁.A C₂.A) i) l
  · simp only [toRealMat, ConPolyZono.andA, Fin.append_left, Fin.append_right,
      Pi.zero_apply, toReal_zero]
  · simp only [toRealMat, ConPolyZono.andA, Fin.append_left, Fin.append_right,
      Pi.zero_apply, toReal_zero]
  · simp only [toRealMat, ConPolyZono.andA, Fin.append_right]
    exact ConPolyZono.toReal_agreeRow C₁ C₂ i l

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
