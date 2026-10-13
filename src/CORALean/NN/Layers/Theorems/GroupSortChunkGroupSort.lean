import CORALean.NN.Layers.Operations.GroupSort

/-!
# A chunk of the group-sorted vector is the sorted chunk

The `k`-th chunk of `groupSort g x` is the `k`-th chunk of `x` sorted: the sorted list read back
entry by entry, at positions `k·g + r` with `r < g`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem groupSortChunk_groupSort {g : ℕ} (hg : 0 < g) (x : Vec ℝ n) (k : ℕ) :
    groupSortChunk g (groupSort g x) k =
      (groupSortChunk g x k).mergeSort (fun a b => decide (a ≤ b)) := by -- --- PROOF ---
  apply List.ext_getElem
  · simp [groupSortChunk]
  · intro r h1 h2
    have hr : r < g := by
      have : r < min g (n - k * g) := by simpa [groupSortChunk] using h1
      omega
    have hd : (k * g + r) / g = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hr, zero_add]
    have hm : (k * g + r) % g = r := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    simp only [groupSortChunk, List.getElem_ofFn, groupSort, hm]
    generalize hk : (k * g + r) / g = k'
    rw [hd] at hk
    subst hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [groupSortChunk] using h2)]
    exact Option.getD_some

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
