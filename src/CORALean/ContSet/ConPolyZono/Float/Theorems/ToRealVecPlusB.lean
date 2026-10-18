module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Float.Theorems.Basic

@[expose] public section

/-!
# `plusB` reads back to the exact layer's

The right-hand sides, or the slacks, side by side: both blocks read back by `toRealVec_append`.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Two stored vectors side by side read back as the two read back side by side. -/
theorem ConPolyZono.toRealVec_plusB {m₁ m₂ : ℕ} (b₁ : Vec 𝕋 m₁) (b₂ : Vec 𝕋 m₂) :
    toRealVec (ConPolyZono.plusB b₁ b₂)
      = Real.ConPolyZono.plusB (toRealVec b₁) (toRealVec b₂) :=
  ConPolyZono.toRealVec_append b₁ b₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
