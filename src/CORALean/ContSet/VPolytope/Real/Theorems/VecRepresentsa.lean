module

public import CORALean.ContSet.VPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# `representsa` of a matrix polytope is that of its vectorisation

CORA's `matPolytope/representsa` hands `polytope(matP)` to the vector class, so whatever the class
answers about the set is the answer. The vectorisation is a linear equivalence, which preserves the
set (`vec_exact`), so the set is empty, or a single matrix, exactly when the stacked set is empty or
the stacked matrix. The other types of CORA's `representsa` are not modelled for V-polytopes.

## Inputs
* `P` – matrix polytope

## Hypotheses
* none

## Conclusion
* emptiness and single-matrix status agree with the vectorisation
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Stacking the entries does not change whether the polytope is empty or a single matrix. -/
theorem VPolytope.vec_representsa (P : VPolytope (Mat ℝ n m)) :
    (P.vec.construct = ∅ ↔ P.construct = ∅) ∧
      ∀ A : Mat ℝ n m, (P.vec.construct = {matVecEquiv A} ↔ P.construct = {A}) := by
  refine ⟨?_, fun A => ?_⟩
  · rw [← VPolytope.vec_exact, Set.image_eq_empty]
  · rw [← VPolytope.vec_exact, ← Set.image_singleton]
    exact matVecEquiv.injective.image_injective.eq_iff

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
