module

public import CORALean.NN.Layers.Operations.Basic
public import CORALean.NN.Layers.Theorems.SumIteZero
public import CORALean.NN.Layers.Theorems.ToRealIteZero

@[expose] public section

/-!
# A sum leaving one index out, bounded below

Downward against any real bound on the terms, which is what the softmax layer has.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem sumOffDown_le (i : Fin n) (v : Fin n → 𝕋) (h : Fin n → ℝ)
    (hv : ∀ j, j ≠ i → toReal (v j) ≤ h j) :
    toReal (sumOffDown i v) ≤ ∑ j ∈ Finset.univ.erase i, h j := by -- --- PROOF ---
  refine le_trans (sumDown_le_sum _) ?_
  rw [Finset.sum_congr rfl fun j _ => toReal_ite_zero v i j, ← sum_ite_zero i h]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j = i
  · rw [if_pos hj, if_pos hj]
  · rw [if_neg hj, if_neg hj]
    exact hv j hj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
