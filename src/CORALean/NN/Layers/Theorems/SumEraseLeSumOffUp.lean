module

public import CORALean.NN.Layers.Operations.SumOffUp
public import CORALean.NN.Layers.Theorems.SumIteZero
public import CORALean.NN.Layers.Theorems.ToRealIteZero

@[expose] public section

/-!
# A sum leaving one index out, bounded above

The zeroed term contributes nothing, so the rounded-up sum bounds the erased one.

## Inputs
* `i` – omitted index
* `v` – summands

## Hypotheses
* none

## Conclusion
* the sum without the omitted term is at most the rounded-up bound
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

theorem sum_erase_le_sumOffUp (i : Fin n) (v : Fin n → 𝕋) : -- --- CONCL ---
    ∑ j ∈ Finset.univ.erase i, toReal (v j) ≤ toReal (sumOffUp i v) := by -- --- PROOF ---
  have h : ∑ j, toReal (if j = i then zero else v j)
      = ∑ j ∈ Finset.univ.erase i, toReal (v j) := by
    rw [Finset.sum_congr rfl fun j _ => toReal_ite_zero v i j]
    exact sum_ite_zero i fun j => toReal (v j)
  rw [← h]
  exact sum_le_sumUp _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
