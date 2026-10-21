module

public import CORALean.ContSet.HPolytope.Real.Theorems.MemIntersection

@[expose] public section

/-!
# `HPolytope.intersection` is exactly the intersection

`mem_intersection_iff` read as a set equality. Intersection is the operation a halfspace
description is exact under and a vertex description is not, which is why the
tree converts to this representation to intersect.

This is [1, Eq. 36]: the intersection of two H-polytopes stacks their constraints.

## Inputs
* `P₁` – H-polytope
* `P₂` – H-polytope

## Hypotheses
* none

## Conclusion
* `HPolytope.intersection` is exactly the intersection

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.intersection_exact (P₁ P₂ : HPolytope α) :
    P₁.construct ∩ P₂.construct = (P₁.intersection P₂).construct :=
  Set.ext fun _ => HPolytope.mem_intersection_iff.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
