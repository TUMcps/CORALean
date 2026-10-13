import CORALean.ContSet.ConPolyZono.Float.Operations.Plus

/-!
# Appending two float vectors and reading back commutes
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

theorem ConPolyZono.toRealVec_append {m₁ m₂ : ℕ} (b₁ : Vec 𝕋 m₁) (b₂ : Vec 𝕋 m₂) :
    toRealVec (Fin.append b₁ b₂) = Fin.append (toRealVec b₁) (toRealVec b₂) := by
  refine funext (Fin.addCases (fun i => ?_) (fun i => ?_)) <;>
    simp only [toRealVec, Fin.append_left, Fin.append_right]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
