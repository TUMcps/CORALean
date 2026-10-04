import CORALean.Specification.STL.Operations.ClauseInsert
import CORALean.Specification.STL.Theorems.BranchHoldsMerge

/-!
# Inserting a branch in a clause

[1, Lemma 2]: some branch of `insert b cl` holds of `ξ` iff `b` does or some branch of `cl` does:
merging branches of one `j` keeps the disjunction.

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

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Clause.holds_insert (c : ℝ≥0) (b : STL.Branch X) (cl : STL.Clause X)
    (ξ : ℝ≥0 → X) : (∃ b' ∈ STL.Clause.insert b cl, b'.Holds c ξ) ↔
      b.Holds c ξ ∨ ∃ b' ∈ cl, b'.Holds c ξ := by -- --- PROOF ---
  induction cl with
  | nil => simp [STL.Clause.insert]
  | cons b' rest ih =>
    by_cases h : b'.j = b.j
    · -- same `j`: the merged branch stands for both
      simp only [STL.Clause.insert, h, if_true, List.mem_cons, exists_eq_or_imp,
        STL.Branch.holds_merge c h]
      rw [or_assoc]
      exact or_left_comm
    · simp only [STL.Clause.insert, h, if_false, List.mem_cons, exists_eq_or_imp, ih]
      exact or_left_comm


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
