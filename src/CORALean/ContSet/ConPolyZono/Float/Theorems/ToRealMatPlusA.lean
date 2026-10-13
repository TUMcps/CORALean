module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
public import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA

@[expose] public section

/-!
# The constraint matrix `plusA` reads back to the exact layer's

`plusA` copies entries and writes `zero` in the off-blocks, so reading it back
is the exact layer's `plusA` of the two read-back matrices.
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

theorem ConPolyZono.toRealMat_plusA {m₁ s₁ m₂ s₂ : ℕ} (A₁ : Mat 𝕋 m₁ s₁)
    (A₂ : Mat 𝕋 m₂ s₂) :
    toRealMat (ConPolyZono.plusA A₁ A₂)
      = Real.ConPolyZono.plusA (toRealMat A₁) (toRealMat A₂) := by -- --- PROOF ---
  have key : ∀ i l, toRealMat (ConPolyZono.plusA A₁ A₂) i l
      = Real.ConPolyZono.plusA (toRealMat A₁) (toRealMat A₂) i l := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) <;>
      refine Fin.addCases (fun l => ?_) (fun l => ?_) <;>
      simp only [toRealMat, ConPolyZono.plusA, Real.ConPolyZono.plusA,
        Fin.append_left, Fin.append_right, Pi.zero_apply, toReal_zero]
  exact funext fun i => funext fun l => key i l

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
