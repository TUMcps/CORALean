module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.QMemConstruct
public import CORALean.ContSet.ConZonotope.Real.Theorems.ExistsConstructEqIffHPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeVPolytopeExact
public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidExistsNotVPolytope
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsCompact
public import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff

@[expose] public section

/-!
# An ellipsoid that is no halfspace description

A bounded halfspace description is a constrained zonotope
(`ConZonotope.exists_construct_eq_iff_hPolytope`), and a nonempty constrained zonotope is a polytope
by vertices (`ConZonotope.vPolytope_exact`), which the unit disc is not
(`Ellipsoid.exists_not_vPolytope`).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* some planar ellipsoid is no halfspace polytope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.exists_not_hPolytope :
    ∃ E : Ellipsoid 2, ¬ ∃ P : HPolytope (Vec ℝ 2), P.construct = E.construct := by -- --- PROOF ---
  obtain ⟨E, hE⟩ := Ellipsoid.exists_not_vPolytope
  refine ⟨E, ?_⟩
  rintro ⟨P, hP⟩
  -- the halfspace description is bounded, so a constrained zonotope
  obtain ⟨cZ, hcZ⟩ := ConZonotope.exists_construct_eq_iff_hPolytope.mpr
    ⟨P, hP, E.isCompact_construct.isBounded⟩
  -- the center is a point of it, so its coefficient domain is nonempty
  have hc : E.q ∈ E.construct := E.q_mem_construct
  obtain ⟨β, hβ, hβP, -⟩ := hcZ ▸ hc
  exact hE ⟨cZ.vPolytope ⟨β, ConZonotope.mem_domain_iff.mpr ⟨hβ, hβP⟩⟩,
    (ConZonotope.vPolytope_exact cZ _).trans hcZ⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
