import CORALean.ContSet.Taylm.Float.Operations.OptBnbAdv
import CORALean.ContSet.Taylm.Float.Theorems.BranchAndBoundMem

/-!
# `Taylm.optBnbAdv` encloses

Outer: a function the float model encloses lies in the result at every point of the normalized
box; sound for every `ε` and `fuel`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.optBnbAdv_mem {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (ε : 𝕋)
    (fuel : ℕ) {t : Vec ℝ n} (ht : t ∈ Real.Taylm.box n) :
    toReal (T.optBnbAdv ε fuel).1 ≤ f t ∧ f t ≤ toReal (T.optBnbAdv ε fuel).2 := by -- --- PROOF ---
  -- the normalized box as a float box
  have hX : Taylm.InBox (fun _ => (neg one, one) : Fin n → 𝕋 × 𝕋) t := fun k => by
    have := abs_le.1 (ht k)
    simp only [toReal_neg, toReal_one]
    exact this
  have hb := Taylm.branchAndBound_mem T.terms (fun _ => (neg one, one)) ε true fuel hX
  have hr := h t ht
  simp only [Taylm.nominal, Real.Taylm.poly] at hr
  have h1 := addDown_le_add
    (Taylm.branchAndBound T.terms (fun _ => (neg one, one)) ε true fuel).1 T.remInf
  have h2 := add_le_addUp
    (Taylm.branchAndBound T.terms (fun _ => (neg one, one)) ε true fuel).2 T.remSup
  simp only [Taylm.optBnbAdv]
  constructor <;> linarith [hb.1, hb.2, hr.1, hr.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
