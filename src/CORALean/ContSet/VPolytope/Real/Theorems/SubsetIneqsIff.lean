module

public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.HPolytope.Real.Theorems.Convex
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# V-polytope in H-polytope

[1, Eq. 6]: `⟨V⟩ ⊆ ⟨A, b⟩` exactly when `A vⱼ ≤ b` for every point — one matrix-vector product
per point, by convexity of the halfspaces.

## Inputs
* `P` – polytope
* `A` – inequality matrix
* `b` – inequality offsets

## Hypotheses
* none

## Conclusion
* `P` lies in `{A x ≤ b}` iff every vertex satisfies it

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral Operations
      in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for Continuous
      and Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.construct_subset_ineqs_iff (P : VPolytope (Vec ℝ n)) (A : Mat ℝ q n)
    (b : Vec ℝ q) :
    P.construct ⊆ (HPolytope.ineqs A b).construct ↔ ∀ l, A *ᵥ P.V l ≤ b := by
  rw [P.construct_eq_convexHull, (HPolytope.ineqs A b).convex_construct.convexHull_subset_iff,
    Set.range_subset_iff]
  exact forall_congr' fun l => HPolytope.mem_ineqs_iff

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
