import CORALean.Specification.STL.Operations.ClauseInsert

/-!
# The disjunction of two clauses

[1, Lemma 2]: `⋁ⱼ X_c^j(…) ∨ ⋁ⱼ X_c^j(…)` as one clause, the branches of the second added to the
first.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The clause holding the branches of both, those of equal `j` merged. -/
def STL.Clause.merge (cl₁ cl₂ : STL.Clause X) : STL.Clause X :=
  cl₂.foldr STL.Clause.insert cl₁


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
