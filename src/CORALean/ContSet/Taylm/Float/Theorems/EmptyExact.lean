module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.EmptyExact

@[expose] public section

/-!
# `Taylm.empty` denotes `∅`, over a floating-point scalar
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.empty_exact (hn : 0 < n) :
    Taylm.construct (Taylm.empty n : Fin n → Taylm 𝕋 n) = ∅ := by -- --- PROOF ---
  have h : (fun i => (Taylm.empty n i : Taylm 𝕋 n).nominal) = Real.Taylm.empty n := by
    funext i
    simp [Taylm.empty, Taylm.nominal, Real.Taylm.empty, toReal_one, toReal_zero]
  show Real.Taylm.construct (fun i => (Taylm.empty n i : Taylm 𝕋 n).nominal) = ∅
  rw [h]
  exact Real.Taylm.empty_exact hn

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
