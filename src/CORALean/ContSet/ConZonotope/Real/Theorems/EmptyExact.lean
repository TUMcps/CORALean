import CORALean.ContSet.ConZonotope.Real.Operations.Empty
import CORALean.ContSet.HPolytope.Real.Operations.ConstructEmptySet

/-!
# `ConZonotope.empty` denotes the empty set


-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.empty_exact (n : ℕ) : (ConZonotope.empty n).construct = ∅ := by -- --- PROOF ---
  ext x
  simp only [ConZonotope.construct, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨β, -, hβ, -⟩
  have h : β ∈ (HPolytope.emptySet (Vec ℝ 0)).construct := hβ
  rw [HPolytope.construct_emptySet] at h
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
