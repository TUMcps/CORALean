module

public import CORALean.NN.Layers.Operations.GroupSortFloat

@[expose] public section

/-!
# The chunk of the sorted vector is the sorted chunk

Chunk `k` of `groupSortFloat g x` is chunk `k` of `x` sorted by `le`, for `g > 0`.

## Inputs
* `g` – group size
* `x` – float input vector
* `k` – group index

## Hypotheses
* `hg` – group size is positive

## Conclusion
* a group of the sorted vector is the sorted group
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem groupSortChunkFloat_groupSortFloat {g : ℕ} (hg : 0 < g) (x : Vec 𝕋 n)
    (k : ℕ) : -- --- CONCL ---
    aux_groupSortChunkFloat g (groupSortFloat g x) k =
      (aux_groupSortChunkFloat g x k).mergeSort FloatOps.le := by -- --- PROOF ---
  apply List.ext_getElem
  · simp [aux_groupSortChunkFloat]
  · intro r h1 h2
    -- the position `r` lies in the chunk, so its quotient and remainder by `g` are `k` and `r`
    have hr : r < g := by
      have : r < min g (n - k * g) := by simpa [aux_groupSortChunkFloat] using h1
      omega
    have hd : (k * g + r) / g = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hr, zero_add]
    have hm : (k * g + r) % g = r := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    simp only [aux_groupSortChunkFloat, List.getElem_ofFn, groupSortFloat, hm]
    generalize hk : (k * g + r) / g = k'
    rw [hd] at hk
    subst hk
    -- reading entry `r` of the sorted chunk
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa [aux_groupSortChunkFloat] using h2)]
    exact Option.getD_some

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
