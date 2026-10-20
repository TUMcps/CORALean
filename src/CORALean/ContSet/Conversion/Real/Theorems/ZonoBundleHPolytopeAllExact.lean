module

public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeHPolytopeFacetsExact
public import CORALean.ContSet.HPolytope.Real.Theorems.MemFoldlIntersectionIff
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEqIInter

@[expose] public section

/-!
# CORA's `polytope(zB)` is the bundle, for members whose generators span

The fold of intersections holds a point exactly when every member's facet polytope does
(`mem_foldl_intersection_iff`, the start being the whole space), and each of those is its member
(`Zonotope.hPolytopeFacets_exact`).

## Inputs
* `zB` – zonotope bundle

## Hypotheses
* `hspan` – generators of each member span the space

## Conclusion
* intersected facet polytopes equal the bundle
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The members' facet polytopes, intersected, are the bundle. -/
theorem ZonoBundle.hPolytopeAll_exact (zB : ZonoBundle (Vec ℝ (n + 1)))
    (hspan : ∀ i, Submodule.span ℝ (Set.range (zB.Z i).G) = ⊤) : -- --- CONCL ---
    zB.hPolytopeAll.construct = zB.construct := by -- --- PROOF ---
  ext x
  rw [ZonoBundle.hPolytopeAll, HPolytope.mem_foldl_intersection_iff, ZonoBundle.construct_eq_iInter,
    Set.mem_iInter]
  -- the whole space holds every point; each member's rows are that member
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · rintro ⟨_, h⟩ i
    rw [← (zB.Z i).hPolytopeFacets_exact (hspan i)]
    exact h i
  · intro h
    refine ⟨⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => ?_⟩
    rw [(zB.Z i).hPolytopeFacets_exact (hspan i)]
    exact h i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
