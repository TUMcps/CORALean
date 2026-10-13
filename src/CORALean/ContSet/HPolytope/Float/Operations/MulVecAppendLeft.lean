import CORALean.ContSet.HPolytope.Float.Operations.Intersection

/-!
# A row of a concatenated constraint matrix, on the left block
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

/-- A row of a concatenated constraint matrix, applied to a point. -/
theorem HPolytope.mulVec_append_left {m₁ m₂ : ℕ} (A₁ : Mat 𝕋 m₁ n) (A₂ : Mat 𝕋 m₂ n)
    (x : Vec ℝ n) (j : Fin m₁) :
    (toRealMat (Fin.append A₁ A₂) *ᵥ x) (Fin.castAdd m₂ j) = (toRealMat A₁ *ᵥ x) j := by
  show ∑ k, toReal (Fin.append A₁ A₂ (Fin.castAdd m₂ j) k) * x k = _
  rw [Fin.append_left]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
