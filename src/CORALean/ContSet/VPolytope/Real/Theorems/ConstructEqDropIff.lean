import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
import CORALean.Global.DropIdx

/-!
# A redundant point of a V-polytope

[1, Eq. 2]: dropping the `j`-th point leaves the polytope unchanged exactly when that point lies
in the polytope of the others.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.construct_eq_drop_iff (P : VPolytope α) (j : Fin P.k) :
    P.construct = (⟨P.k - 1, fun i => P.V (dropIdx j i)⟩ : VPolytope α).construct ↔
      P.V j ∈ (⟨P.k - 1, fun i => P.V (dropIdx j i)⟩ : VPolytope α).construct := by -- --- PROOF ---
  constructor
  · intro h
    rw [← h]
    exact P.vertex_mem j
  · intro h
    rw [VPolytope.construct_eq_convexHull] at h
    rw [VPolytope.construct_eq_convexHull, VPolytope.construct_eq_convexHull]
    refine Set.Subset.antisymm (convexHull_min ?_ (convex_convexHull ℝ _))
      (convexHull_mono ?_)
    -- every point is either the dropped one or one of the others
    · rintro _ ⟨l, rfl⟩
      revert l
      exact (forall_dropIdx_iff j).mpr ⟨h, fun i => subset_convexHull ℝ _ ⟨i, rfl⟩⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨dropIdx j i, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
