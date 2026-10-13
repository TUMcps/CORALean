module

public import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionA
public import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionA
public import CORALean.ContSet.ConPolyZono.Float.Operations.AgreeRow
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealAgreeRow
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatPlusA

@[expose] public section

/-!
# The constraint matrix `intersectionA` reads back to the exact layer's

Field by field: the `plus` block is the exact layer's `plusA` of the two
read-back matrices, and the agreement block is `toReal_agreeRow` read one row
at a time.
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.toRealMat_intersectionA (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    toRealMat (ConPolyZono.intersectionA cPZ₁ cPZ₂)
      = Real.ConPolyZono.intersectionA (nominal cPZ₁) (nominal cPZ₂) := by -- --- PROOF ---
  -- the exact layer's matrix spelled out, so the four `Fin.addCases` branches below match it
  have hreal : Real.ConPolyZono.intersectionA (nominal cPZ₁) (nominal cPZ₂)
      = fun i => Fin.append
          (fun r => Fin.append (Real.ConPolyZono.plusA (toRealMat cPZ₁.A) (toRealMat cPZ₂.A) r)
            (0 : Fin (cPZ₁.h + cPZ₂.h) → ℝ))
          (fun r => Fin.append (0 : Fin (cPZ₁.s + cPZ₂.s) → ℝ)
            (Real.ConPolyZono.agreeRow (nominal cPZ₁) (nominal cPZ₂) r)) i := rfl
  rw [hreal]
  refine funext (Fin.addCases (fun i => ?_) fun i => ?_) <;>
    refine funext (Fin.addCases (fun l => ?_) fun l => ?_)
  · simp only [toRealMat, ConPolyZono.intersectionA, Fin.append_left]
    exact congrFun (congrFun (ConPolyZono.toRealMat_plusA cPZ₁.A cPZ₂.A) i) l
  · simp only [toRealMat, ConPolyZono.intersectionA, Fin.append_left, Fin.append_right,
      Pi.zero_apply, toReal_zero]
  · simp only [toRealMat, ConPolyZono.intersectionA, Fin.append_left, Fin.append_right,
      Pi.zero_apply, toReal_zero]
  · simp only [toRealMat, ConPolyZono.intersectionA, Fin.append_right]
    exact ConPolyZono.toReal_agreeRow cPZ₁ cPZ₂ i l

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
