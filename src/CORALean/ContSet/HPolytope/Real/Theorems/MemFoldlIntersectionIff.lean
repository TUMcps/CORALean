module

public import CORALean.ContSet.HPolytope.Real.Theorems.MemIntersection

@[expose] public section

/-!
# Membership in a fold of intersections

`and_(.., 'exact')` over a list, as CORA folds the members of a bundle: a point is in the fold
exactly when it is in the start and in every polytope of the list. Induction on the list, one
`mem_intersection_iff` per step.

## Inputs
* `L` – list of polytopes
* `P₀` – H-polytope
* `x` – point

## Hypotheses
* none

## Conclusion
* A point of the folded intersection is a point of the start and of every member
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the folded intersection is a point of the start and of every member. -/
theorem HPolytope.mem_foldl_intersection_iff (L : List (HPolytope α)) (P₀ : HPolytope α)
    (x : α) : -- --- CONCL ---
    x ∈ (L.foldl HPolytope.intersection P₀).construct
      ↔ x ∈ P₀.construct ∧ ∀ P ∈ L, x ∈ P.construct := by -- --- PROOF ---
  induction L generalizing P₀ with
  | nil => simp
  | cons P L ih =>
    rw [List.foldl_cons, ih, HPolytope.mem_intersection_iff]
    simp only [List.mem_cons, forall_eq_or_imp]
    exact and_assoc

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
