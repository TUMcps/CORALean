module

public import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.ZonoBundle_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.ConZonotope_to_VPolytope

@[expose] public section

/-!
# A bundle's corners, at one component — the construction

`ZonoBundle.vPolytope` and `ZonoBundle.vPolytopeAll` are the constructions;
`ZonoBundle_to_VPolytope` states and proves what they guarantee.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ZonoBundle.vPolytope (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) :
    VPolytope (Vec ℝ n) :=
  (zB.zonotope i).vPolytope


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The coefficient domain of `conZonotope(zB)` is nonempty when the bundle is. -/
theorem ZonoBundle.aux_domain_nonempty (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k)
    (hne : zB.construct.Nonempty) :
    (zB.conZonotopeAll hk).domain.construct.Nonempty := by
  obtain ⟨x, hx⟩ := hne
  rw [← ZonoBundle.conZonotopeAll_exact zB hk] at hx
  obtain ⟨β, hb, hP, -⟩ := hx
  exact ⟨β, ConZonotope.mem_domain_iff.mpr ⟨hb, hP⟩⟩

/-- CORA's `vertices_` of a bundle: the vertices of `conZonotope(zB)`. -/
noncomputable def ZonoBundle.vPolytopeAll (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k)
    (hne : zB.construct.Nonempty) : VPolytope (Vec ℝ n) :=
  (zB.conZonotopeAll hk).vPolytope (zB.aux_domain_nonempty hk hne)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
