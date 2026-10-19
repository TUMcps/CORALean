module

public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeHPolytopeFacetsContains
public import CORALean.ContSet.HPolytope.Real.Theorems.MemFoldlIntersectionIff
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEqIInter

@[expose] public section

/-!
# A bundle lies in CORA's `polytope(zB)`

Each member lies in its facet polytope (`Zonotope.hPolytopeFacets_contains`), so a point of every
member lies in every one of them, and so in the fold of their intersections; no spanning needed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every bundle lies in the members' facet polytopes, intersected. -/
theorem ZonoBundle.hPolytopeAll_contains (zB : ZonoBundle (Vec ℝ (n + 1))) :
    zB.construct ⊆ zB.hPolytopeAll.construct := by -- --- PROOF ---
  intro x hx
  rw [ZonoBundle.construct_eq_iInter, Set.mem_iInter] at hx
  rw [ZonoBundle.hPolytopeAll, HPolytope.mem_foldl_intersection_iff]
  -- the whole space, then each member's rows
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
  exact ⟨⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => (zB.Z i).hPolytopeFacets_contains (hx i)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
