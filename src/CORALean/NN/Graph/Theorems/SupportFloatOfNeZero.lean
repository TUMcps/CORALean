module

public import CORALean.NN.Graph.Operations.SupportFloat

@[expose] public section

/-!
# A nonzero entry is on the float support
If the stored entry reads as a nonzero real, `GNN.support` holds there: `le` answers `true` only
when sure, so both directions cannot be certified.

## Inputs
* `A` – float adjacency matrix
* `i` – row node
* `j` – column node

## Hypotheses
* `h` – the entry reads as a nonzero real

## Conclusion
* the entry lies on the float support
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.support_of_ne_zero (A : Mat 𝕋 N N) (i j : Fin N)
    (h : toReal (A i j) ≠ 0) : -- --- CONCL ---
    GNN.support A i j = true := by -- --- PROOF ---
  by_contra hf
  have hb : (le (A i j) zero && le zero (A i j)) = true := by
    simpa [GNN.support] using hf
  rw [Bool.and_eq_true] at hb
  have h1 := toReal_le_of_le hb.1
  have h2 := toReal_le_of_le hb.2
  rw [toReal_zero] at h1 h2
  exact h (le_antisymm h1 h2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
