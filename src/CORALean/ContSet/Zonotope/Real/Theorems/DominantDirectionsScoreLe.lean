import CORALean.ContSet.Zonotope.Real.Operations.DominantDirections

/-!
# `dominantDirections` is the best shortlisted subset

No subset the generator volume filter kept scores below the answer: `priv_volumeFilter` takes the
least `Zonotope.dominantScore` (the volume of the parallelotope the subset encloses `Z` in).

Source: [1].

## References

* [1] `contSet/@zonotope/dominantDirections.m` and its private helpers, CORA (Sep. 2025), by
      M. Althoff (2010). No paper behind the rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.dominantDirections_score_le (Z : Zonotope (Vec ℝ n)) (a b : ℕ) (P : Mat ℝ n n)
    (h : Z.dominantDirections a b = some P)
    (T : Finset (Fin Z.h))
    (hT : T ∈ Z.dominantShortlist (min a (Finset.univ.filter fun j => Z.G j ≠ 0).card)
        (min b (Finset.univ.filter fun j => Z.G j ≠ 0).card)) :
    Z.dominantScore P ≤ Z.dominantScore (Z.generatorMatrix T) := by
  unfold Zonotope.dominantDirections at h
  have hmem : P ∈ List.argmin Z.dominantScore ((Z.dominantShortlist _ _).map Z.generatorMatrix) := h
  exact List.le_of_mem_argmin (List.mem_map_of_mem hT) hmem

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
