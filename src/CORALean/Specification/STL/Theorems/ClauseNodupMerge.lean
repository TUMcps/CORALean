import CORALean.Specification.STL.Operations.ClauseMerge
import CORALean.Specification.STL.Theorems.ClauseNodupInsert

/-!
# Merging two clauses keeps the powers distinct

[1, Lemma 2]: if the `j` of the branches of `cl₁` are distinct, so are those of `cl₁.merge cl₂`,
whatever `cl₂` is.

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Clause.nodup_merge (cl₁ cl₂ : STL.Clause X) (h : (cl₁.map STL.Branch.j).Nodup) :
    ((STL.Clause.merge cl₁ cl₂).map STL.Branch.j).Nodup := by
  induction cl₂ with
  | nil => simpa [STL.Clause.merge] using h
  | cons b rest ih => exact STL.Clause.nodup_insert b _ ih


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
