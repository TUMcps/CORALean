module

public import CORALean.ContSet.ConZonotope.Real.Operations.Empty
public import CORALean.ContSet.HPolytope.Real.Theorems.ToSetEmptySet

@[expose] public section

/-!
# `ConZonotope.empty` denotes the empty set

## Inputs
* `n` – dimension

## Hypotheses
* none

## Conclusion
* the empty constrained zonotope denotes the empty set
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.empty_exact (n : ℕ) : -- --- CONCL ---
    (ConZonotope.empty n).toSet = ∅ := by -- --- PROOF ---
  ext x
  simp only [ConZonotope.toSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨β, -, hβ, -⟩
  have h : β ∈ (HPolytope.emptySet (Vec ℝ 0)).toSet := hβ
  rw [HPolytope.toSet_emptySet] at h
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
