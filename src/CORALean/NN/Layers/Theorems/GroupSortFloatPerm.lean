module

public import CORALean.NN.Layers.Theorems.GroupSortChunkFloatGroupSortFloat

@[expose] public section

/-!
# The float group sort permutes every chunk

Every chunk of `groupSortFloat g x` is a permutation of the same chunk of `x`: sorting moves
entries and computes none, so this holds whatever `le` answers, and at the real values they
denote. Under an exact `le` each chunk is also ascending (`groupSortFloat_sorted`).

## Inputs
* `g` – group size
* `x` – float input vector
* `k` – group index

## Hypotheses
* `hg` – group size is positive

## Conclusion
* each group of the result is a permutation of the input group
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem groupSortFloat_perm {g : ℕ} (hg : 0 < g) (x : Vec 𝕋 n) (k : ℕ) :
    (aux_groupSortChunkFloat g (groupSortFloat g x) k).Perm (aux_groupSortChunkFloat g x k) := by
  rw [groupSortChunkFloat_groupSortFloat hg]
  exact List.mergeSort_perm _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
