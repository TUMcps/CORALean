import CORALean.ContSet.Taylm.Float.Operations.Uminus
import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNeg

/-!
# `Taylm.uminus` encloses the negation
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

theorem Taylm.uminus_outer {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.uminus.Encloses fun t => -f t := by -- --- PROOF ---
  intro t ht
  have a := h t ht
  have e : (T.terms.map fun a => (neg a.1, a.2)).map (fun a => (toReal a.1, a.2))
      = (T.terms.map fun a => (toReal a.1, a.2)).map fun a => (-a.1, a.2) := by
    simp [toReal_neg]
  simp only [Taylm.uminus, Taylm.nominal, Real.Taylm.poly, e, Real.Taylm.polyOf_neg,
    toReal_neg] at *
  constructor <;> linarith [a.1, a.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
