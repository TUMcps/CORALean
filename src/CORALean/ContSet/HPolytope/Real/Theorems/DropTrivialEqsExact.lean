module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.RestrictConstruct

@[expose] public section

/-!
# `HPolytope.dropTrivialEqs` loses nothing

Every point meets a row `0 = 0`, so dropping those rows leaves the set as it was
(`HPolytope.restrict_construct` with every inequality and the other equalities kept).
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Dropping the equality rows `0 = 0` leaves the set unchanged. -/
theorem HPolytope.dropTrivialEqs_exact (P : HPolytope α) :
    P.dropTrivialEqs.construct = P.construct := by -- --- PROOF ---
  classical
  rw [HPolytope.dropTrivialEqs, HPolytope.restrict_construct]
  ext x
  simp only [Set.mem_setOf_eq, Finset.mem_univ, true_implies, Finset.mem_filter, true_and]
  refine and_congr Iff.rfl ⟨fun h i => ?_, fun h i _ => h i⟩
  -- a row `0 = 0` holds at every point
  by_cases hi : P.Ae i = 0 ∧ P.be i = 0
  · rw [hi.1, hi.2]
    rfl
  · exact h i hi

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
