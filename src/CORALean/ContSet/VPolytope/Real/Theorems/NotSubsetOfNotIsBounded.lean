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

* [1] [M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for
      Continuous and Hybrid Systems,
      2024.](../../../../../../references/2024/wetzlinger-arch-polyhedral-operations.md)
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
