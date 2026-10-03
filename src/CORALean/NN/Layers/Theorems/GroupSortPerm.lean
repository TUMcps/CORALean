import CORALean.NN.Layers.Theorems.GroupSortChunkGroupSort

/-!
# Group sort permutes each chunk and sorts it

CORA's `nnGroupSortLayer` sorts each chunk of `groupSize` entries ascending: the chunk of the
result is a permutation of the chunk of the input (nothing is lost, nothing is invented), and it
is sorted.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem groupSort_perm {g : ℕ} (hg : 0 < g) (x : Vec ℝ n) (k : ℕ) :
    (groupSortChunk g (groupSort g x) k).Perm (groupSortChunk g x k) := by
  rw [groupSortChunk_groupSort hg]
  exact List.mergeSort_perm _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
