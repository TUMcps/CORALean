import CORALean.ContSet.Zonotope.Real.Operations.DominantDirections

/-!
# `dominantDirections` is a shortlisted subset's generators

The answer is the matrix of one of the subsets the generator volume filter kept.

Source: [1].

## References

* [1] `contSet/@zonotope/dominantDirections.m` and its private helpers, CORA (Sep. 2025), by
      M. Althoff (2010). No paper behind the rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.dominantDirections_mem_shortlist (Z : Zonotope (Vec ℝ n)) (a b : ℕ) (P : Mat ℝ n n)
    (h : Z.dominantDirections a b = some P) :
    ∃ T ∈ Z.dominantShortlist (min a (Finset.univ.filter fun j => Z.G j ≠ 0).card)
        (min b (Finset.univ.filter fun j => Z.G j ≠ 0).card), P = Z.generatorMatrix T := by
  unfold Zonotope.dominantDirections at h
  have hmem : P ∈ List.argmin Z.dominantScore ((Z.dominantShortlist _ _).map Z.generatorMatrix) := h
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp (List.argmin_mem hmem)
  exact ⟨T, hT, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
