module

public import CORALean.ContSet.VPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# An unbounded set lies in no V-polytope

[1, Sec. 4.2 (unbounded)]: H-polyhedron in V-polytope containment can be disproved at once when the
polyhedron is unbounded, a V-polytope being bounded.

## Inputs
* `S` – set
* `P` – polytope

## Hypotheses
* `hS` – `S` unbounded

## Conclusion
* `S` is not contained in `P`

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.not_subset_of_not_isBounded {S : Set α} (hS : ¬ Bornology.IsBounded S)
    (P : VPolytope α) : ¬ S ⊆ P.construct :=
  fun h => hS (P.isBounded_construct.subset h)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
