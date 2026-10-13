import CORALean.ContSet.Taylm.Float.Operations.Plus

/-!
# `Taylm.plus` encloses the sum
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.plus_outer {T₁ T₂ : Taylm 𝕋 n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g) : (T₁.plus T₂).Encloses fun t => f t + g t := by -- --- PROOF ---
  intro t ht
  have a₁ := h₁ t ht
  have a₂ := h₂ t ht
  have := addDown_le_add T₁.remInf T₂.remInf
  have := add_le_addUp T₁.remSup T₂.remSup
  simp only [Taylm.plus, Taylm.nominal, Real.Taylm.poly, List.map_append,
    Real.Taylm.polyOf_append] at *
  constructor <;> linarith [a₁.1, a₁.2, a₂.1, a₂.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
