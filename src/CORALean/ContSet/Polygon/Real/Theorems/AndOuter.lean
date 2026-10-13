import CORALean.ContSet.Polygon.Real.Operations.And
import CORALean.ContSet.Polygon.Real.Theorems.AndRegion
import CORALean.ContSet.VPolytope.Real.Theorems.IntersectionOuter

/-!
# `Polygon.and` encloses the intersection

Outer only: the directions need not contain the facet normals. `Polygon.and_region` is the exact
region identity.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

open scoped Classical in
theorem Polygon.and_outer {q : ℕ} (P Q : Polygon) (Aq : Fin q → (Vec ℝ 2 →ₗ[ℝ] ℝ)) :
    ContSet.construct P ∩ ContSet.construct Q ⊆
      ContSet.construct (Polygon.and P Q Aq) := by -- --- PROOF ---
  rw [Polygon.and_region]
  intro x hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨p, hp, r, hr, hx⟩ := hx
  refine SetUnion.mem_construct.mpr
    ⟨VPolytope.intersection p r Aq Aq, ?_, VPolytope.intersection_outer p r Aq Aq hx⟩
  exact List.mem_map.mpr ⟨(p, r), List.mem_product.mpr ⟨hp, hr⟩, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
