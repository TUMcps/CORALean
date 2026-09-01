import CORALean.ContSet.VPolytope.Operations.LinComb
import CORALean.ContSet.VPolytope.Theorems.ConvexHull

/-!
# `VPolytope.linComb` encloses every segment between the two

Each argument's vertices are vertices of the result, so each argument is
contained in it; a segment between two points of a convex set stays inside, and
the result is convex.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

theorem VPolytope.aux_subset_linComb_left (P₁ P₂ : VPolytope α) :
    P₁.construct ⊆ (P₁.linComb P₂).construct := by
  rw [VPolytope.construct_eq_convexHull P₁]
  refine convexHull_min (Set.range_subset_iff.mpr fun j => ?_) (VPolytope.convex_construct _)
  have h := VPolytope.vertex_mem (P₁.linComb P₂) (Fin.castAdd P₂.k j)
  rwa [show (P₁.linComb P₂).V (Fin.castAdd P₂.k j) = P₁.V j from
    Fin.append_left P₁.V P₂.V j] at h

theorem VPolytope.aux_subset_linComb_right (P₁ P₂ : VPolytope α) :
    P₂.construct ⊆ (P₁.linComb P₂).construct := by
  rw [VPolytope.construct_eq_convexHull P₂]
  refine convexHull_min (Set.range_subset_iff.mpr fun j => ?_) (VPolytope.convex_construct _)
  have h := VPolytope.vertex_mem (P₁.linComb P₂) (Fin.natAdd P₁.k j)
  rwa [show (P₁.linComb P₂).V (Fin.natAdd P₁.k j) = P₂.V j from
    Fin.append_right P₁.V P₂.V j] at h

theorem VPolytope.linComb_outer (P₁ P₂ : VPolytope α) :
    segments P₁.construct P₂.construct ⊆ (P₁.linComb P₂).construct := by
  rintro _ ⟨y₁, hy₁, y₂, hy₂, lam, ⟨hlo, hup⟩, rfl⟩
  exact VPolytope.convex_construct _ (VPolytope.aux_subset_linComb_left P₁ P₂ hy₁)
    (VPolytope.aux_subset_linComb_right P₁ P₂ hy₂) hlo (by linarith) (by ring)

end CORALean.Real
