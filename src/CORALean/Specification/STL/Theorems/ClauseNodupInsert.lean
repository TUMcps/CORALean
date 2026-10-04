import CORALean.Specification.STL.Operations.ClauseInsert

/-!
# Inserting keeps the powers distinct

If the `j` of the branches of a clause are distinct, so are those of `insert b cl`: [1, Lemma 2]
needs one disjunct per `j`, and merging is what provides it.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A power of `insert b cl` is `b`'s or one of `cl`'s. -/
theorem STL.Clause.aux_mem_map_j_insert (b : STL.Branch X) (cl : STL.Clause X) (x : ℕ)
    (h : x ∈ (STL.Clause.insert b cl).map STL.Branch.j) :
    x = b.j ∨ x ∈ cl.map STL.Branch.j := by -- --- PROOF ---
  induction cl with
  | nil => simpa [STL.Clause.insert] using h
  | cons b' rest ih =>
    by_cases hj : b'.j = b.j
    · simp only [STL.Clause.insert, hj, if_true, List.map_cons, List.mem_cons,
        STL.Branch.merge] at h ⊢
      exact h.elim Or.inl fun h => Or.inr (Or.inr h)
    · simp only [STL.Clause.insert, hj, if_false, List.map_cons, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · rcases ih h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Clause.nodup_insert (b : STL.Branch X) (cl : STL.Clause X)
    (h : (cl.map STL.Branch.j).Nodup) :
    ((STL.Clause.insert b cl).map STL.Branch.j).Nodup := by -- --- PROOF ---
  induction cl with
  | nil => simp [STL.Clause.insert]
  | cons b' rest ih =>
    rw [List.map_cons, List.nodup_cons] at h
    by_cases hj : b'.j = b.j
    · simpa [STL.Clause.insert, hj, STL.Branch.merge] using h
    · -- the head's power differs from `b`'s and is not among the rest's
      simp only [STL.Clause.insert, hj, if_false, List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih h.2⟩
      rcases STL.Clause.aux_mem_map_j_insert b rest _ hm with e | e
      · exact hj e
      · exact h.1 e


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
