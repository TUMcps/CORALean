import CORALean.ContSet.Taylm.Float.Operations.Bounds
import CORALean.ContSet.Taylm.Float.Theorems.PolyBoundsMem

/-!
# An enclosed function stays in the float `bounds` on the box
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

theorem Taylm.bounds_mem {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) {t : Vec ℝ n}
    (ht : t ∈ Real.Taylm.box n) :
    toReal T.bounds.1 ≤ f t ∧ f t ≤ toReal T.bounds.2 := by -- --- PROOF ---
  have h₁ := h t ht
  have h₂ := Taylm.polyBounds_mem T.terms ht
  have := addDown_le_add (Taylm.polyBounds T.terms).1 T.remInf
  have := add_le_addUp (Taylm.polyBounds T.terms).2 T.remSup
  simp only [Taylm.bounds, Taylm.nominal, Real.Taylm.poly] at *
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
