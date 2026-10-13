module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
public import CORALean.ContSet.ConPolyZono.Float.Operations.PlusB
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealVecAppend

@[expose] public section

/-!
# The bound `plusB` reads back to the exact layer's

Both blocks read back by `toRealVec_append`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.nominal_plusB {m₁ m₂ : ℕ} (b₁ : Interval (Vec 𝕋 m₁))
    (b₂ : Interval (Vec 𝕋 m₂)) :
    (ConPolyZono.plusB b₁ b₂).nominal = Real.ConPolyZono.plusB b₁.nominal b₂.nominal := by
  simp only [ConPolyZono.plusB, Interval.nominal, RealImage.realImage, Real.ConPolyZono.plusB]
  rw [ConPolyZono.toRealVec_append, ConPolyZono.toRealVec_append]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
