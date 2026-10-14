module

public import CORALean.ContSet.Taylm.Float.Operations.OptBnb
public import CORALean.ContSet.Taylm.Float.Theorems.BranchAndBoundMem

@[expose] public section

/-!
# `Taylm.optBnb` encloses

Outer: a function the float model encloses lies in the result at every point of the normalized
box. The branch and bound's range of the polynomial plus the remainder, the ends rounded outward;
sound for every `ε` and `fuel`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.optBnb_mem {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (ε : 𝕋) (fuel : ℕ)
    {t : Vec ℝ n} (ht : t ∈ Real.Taylm.box n) :
    toReal (T.optBnb ε fuel).inf ≤ f t ∧ f t ≤ toReal (T.optBnb ε fuel).sup := by -- --- PROOF ---
  -- the normalized box as a float box
  have hX : Taylm.InBox (fun _ => ⟨neg one, one⟩ : Fin n → Interval 𝕋) t := fun k => by
    have := abs_le.1 (ht k)
    simp only [toReal_neg, toReal_one]
    exact this
  have hb := Taylm.branchAndBound_mem T.terms (fun _ => ⟨neg one, one⟩) ε false fuel hX
  have hr := h t ht
  simp only [Taylm.nominal, Real.Taylm.poly] at hr
  have h1 := addDown_le_add (Taylm.branchAndBound T.terms (fun _ => ⟨neg one,
      one⟩) ε false fuel).inf
    T.remInf
  have h2 := add_le_addUp (Taylm.branchAndBound T.terms (fun _ => ⟨neg one, one⟩) ε false fuel).sup
    T.remSup
  simp only [Taylm.optBnb]
  constructor <;> linarith [hb.1, hb.2, hr.1, hr.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
