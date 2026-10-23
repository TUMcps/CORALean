module

public import CORALean.ContSet.VPolytope.Real.Operations.EmptySet
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `VPolytope.emptySet` denotes `∅`

No coefficient family over an empty index sums to one, so the vertex list
denotes nothing.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the polytope with no vertices denotes the empty set
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.construct_emptySet : -- --- CONCL ---
    (VPolytope.emptySet α).construct = ∅ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨β, -, hsum, -⟩
  -- ascribed at the projection spelling of the count, which is `0` only by defeq
  have hz : ∑ j : Fin (VPolytope.emptySet α).k, β j = 0 := Fin.sum_univ_zero _
  rw [hz] at hsum
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
