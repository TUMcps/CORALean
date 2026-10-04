import CORALean.Specification.STL.Operations.CNFNext
import CORALean.Specification.STL.Theorems.CNFSatToFormula
import CORALean.Specification.STL.Theorems.BranchHoldsShift

/-!
# The next-operator on a normal form

[1, Sec. 4.1]: `ξ ⊨ₜ X_c a ⇔ ⟨ξ⟩_c ⊨ₜ a` for `a.next`: raising every `j` reads the trace shifted
by `c`.

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

theorem STL.CNF.sat_next (c : ℝ≥0) (a : STL.CNF X) (ξ : ℝ≥0 → X) :
    (a.next.toFormula c).Sat ξ ↔ (a.toFormula c).Sat (Time.shift ξ c) := by
  rw [STL.CNF.sat_toFormula, STL.CNF.sat_toFormula]
  simp only [STL.CNF.next, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, exists_exists_and_eq_and, STL.Branch.holds_shift]


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
