module

public import CORALean.ContSet.Conversion.Real.Operations.VPolytope_to_Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.EnclosePointsMaigaMem
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull

@[expose] public section

/-!
# The matrix zonotope of a matrix polytope contains it

Every vertex lies in the enclosing zonotope of the point cloud (`enclosePointsMaiga_mem`), dropping
the zero generators changes nothing (`compactZeros_exact`) and neither does reading the vectors back
as matrices (`map_exact` at the inverse of the vectorisation). A zonotope is convex, so it contains
the hull of the vertices, which is the polytope.

## Inputs
* `P` – matrix vertex polytope
* `dir` – direction chosen from the vertices

## Hypotheses
* none

## Conclusion
* polytope is contained in its matrix zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every member of the matrix polytope lies in the matrix zonotope enclosing its vertices. -/
theorem VPolytope.matZonotope_contains (P : VPolytope (Mat ℝ m n)) [NeZero P.k]
    (dir : (Fin P.k → Vec ℝ (n * m)) → Vec ℝ (n * m)) :
    P.construct ⊆ (P.matZonotope dir).construct := by -- --- PROOF ---
  rw [VPolytope.construct_eq_convexHull]
  refine convexHull_min (Set.range_subset_iff.mpr fun l => ?_) (Zonotope.convex_construct _)
  -- vertex `l` is in the enclosure of the cloud, hence in its image under the inverse reshape
  have h := Zonotope.enclosePointsMaiga_mem dir (fun l => matVecEquiv (P.V l)) l
  rw [← Zonotope.compactZeros_exact] at h
  rw [VPolytope.matZonotope, ← Zonotope.map_exact]
  exact ⟨_, h, by simp⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
