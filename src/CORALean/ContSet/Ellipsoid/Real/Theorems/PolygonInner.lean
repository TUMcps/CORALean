module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Polygon
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Polygon.Real.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# `Ellipsoid.polygon` lies inside the ellipsoid

Inner: each support point `q + G u` has `‖u‖₂ ≤ 1` (`u` is the unit vector `Gᵀ l / ‖Gᵀ l‖₂`, or
`0`), so it is in the ellipsoid, and the ellipsoid is convex, so the hull of the points is. CORA
states neither this nor that the points lie on the boundary; the polygon is an inner
approximation, not an enclosure.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.polygon_inner (E : Ellipsoid 2) (L : List (Vec ℝ 2)) :
    ContSet.construct (E.polygon L) ⊆ E.construct := by -- --- PROOF ---
  rw [Ellipsoid.polygon, Polygon.construct_ofPieces]
  simp only [List.mem_singleton, Set.iUnion_iUnion_eq_left]
  rw [VPolytope.enclosePoints_exact]
  refine convexHull_min ?_ E.convex_construct
  rintro _ ⟨i, rfl⟩
  -- the factor `‖v‖⁻¹ • v` of a support point has length at most one
  refine E.mem_construct ?_
  set v : Vec ℝ E.k := E.Gᵀ *ᵥ L[i] with hv
  rw [norm₂_smul, abs_of_nonneg (inv_nonneg.mpr (norm₂_nonneg v))]
  rcases (norm₂_nonneg v).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [inv_mul_cancel₀ h.ne']

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
