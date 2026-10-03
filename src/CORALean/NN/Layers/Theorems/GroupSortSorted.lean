import CORALean.NN.Layers.Theorems.GroupSortChunkGroupSort

/-!
# Group sort sorts each chunk

Each chunk of `groupSort g x` is ascending, the comparison being the real order, which is
transitive and total. Companion of `groupSort_perm`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem groupSort_sorted {g : ℕ} (hg : 0 < g) (x : Vec ℝ n) (k : ℕ) :
    (groupSortChunk g (groupSort g x) k).Pairwise (· ≤ ·) := by -- --- PROOF ---
  rw [groupSortChunk_groupSort hg]
  have h := List.pairwise_mergeSort (le := fun a b : ℝ => decide (a ≤ b))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at *
      exact le_trans hab hbc)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total a b) (groupSortChunk g x k)
  exact h.imp fun hab => by simpa using hab

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
