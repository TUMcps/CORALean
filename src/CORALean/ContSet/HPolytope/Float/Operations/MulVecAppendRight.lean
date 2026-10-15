module

public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# A row of a concatenated constraint matrix, on the right block
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mulVec_append_right {m₁ m₂ : ℕ} (A₁ : Mat 𝕋 m₁ n) (A₂ : Mat 𝕋 m₂ n)
    (x : Vec ℝ n) (j : Fin m₂) :
    (toRealMat (Fin.append A₁ A₂) *ᵥ x) (Fin.natAdd m₁ j) = (toRealMat A₂ *ᵥ x) j := by
  show ∑ k, toReal (Fin.append A₁ A₂ (Fin.natAdd m₁ j) k) * x k = _
  rw [Fin.append_right]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
