module

public import CORALean.Specification.STL.Theorems.CNFSatToFormula

@[expose] public section

/-!
# Appending normal forms is conjunction

`ξ ⊨ₜ a ++ b ⇔ ξ ⊨ₜ a ∧ ξ ⊨ₜ b`: the `⋀ᵢ` of [1, Sec. 4.1] over two lists of clauses.

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

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.CNF.sat_append (c : ℝ≥0) (a b : STL.CNF X) (ξ : ℝ≥0 → X) :
    ((a ++ b).toFormula c).Sat ξ ↔ (a.toFormula c).Sat ξ ∧ (b.toFormula c).Sat ξ := by
  rw [STL.CNF.sat_toFormula, STL.CNF.sat_toFormula, STL.CNF.sat_toFormula,
    List.forall_mem_append]


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
