module

public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionLowerB
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerB

@[expose] public section

/-!
# `unionLowerB` reads back to the exact layer's

The operand rows' right-hand side `b / 2`, halving being exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The operand rows' right-hand side reads back to the exact layer's, halving being exact. -/
theorem ConPolyZono.toRealVec_unionLowerB {m₁ m₂ : ℕ} (b₁ : Vec 𝕋 m₁) (b₂ : Vec 𝕋 m₂) :
    toRealVec (ConPolyZono.unionLowerB b₁ b₂)
      = Real.ConPolyZono.unionLowerB (toRealVec b₁) (toRealVec b₂) := by
  refine funext (Fin.addCases (fun r => ?_) fun r => ?_) <;>
    simp only [ConPolyZono.unionLowerB, Real.ConPolyZono.unionLowerB, toRealVec, Fin.append_left,
      Fin.append_right, toReal_half] <;> ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
