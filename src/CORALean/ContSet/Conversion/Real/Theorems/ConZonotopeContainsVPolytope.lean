module

public import CORALean.ContSet.ConZonotope.Real.Operations.Domain
public import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff
public import CORALean.ContSet.ConZonotope.Real.Theorems.Convex
public import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompactDomain
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeContainsVPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalContainsVPolytope
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# A constrained zonotope as its vertices

`ConZonotope.contains_vPolytope`: it contains its `vPolytope`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

-- back: each listed vertex comes from a domain vertex, hence from a point of the set
theorem ConZonotope.contains_vPolytope (cZ : ConZonotope α) (hne : cZ.domain.construct.Nonempty) :
    (cZ.vPolytope hne).construct ⊆ cZ.construct := by -- --- PROOF ---
  rw [VPolytope.construct_eq_convexHull]
  refine convexHull_min ?_ cZ.convex_construct
  rintro _ ⟨l, rfl⟩
  have hd : (cZ.domain.vPolytope hne).V l ∈ cZ.domain.construct :=
    cZ.domain.contains_vPolytope hne (by
      rw [VPolytope.construct_eq_convexHull]
      exact subset_convexHull ℝ _ ⟨l, rfl⟩)
  obtain ⟨hb, hP⟩ := ConZonotope.mem_domain_iff.mp hd
  exact ⟨_, hb, hP, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
