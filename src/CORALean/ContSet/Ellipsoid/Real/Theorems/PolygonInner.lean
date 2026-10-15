module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Polygon
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Polygon.Real.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose

@[expose] public section

/-!
# `Ellipsoid.polygon` lies inside the ellipsoid

Inner: each support point `q + Q l / √(lᵀ Q l)` is `q + G u` with `‖u‖₂ ≤ 1` (`u` is the unit vector
`Gᵀ l / ‖Gᵀ l‖₂`, or `0`, `G = Q^(1/2)`), so it is in the ellipsoid, and the ellipsoid is convex, so
the hull of the points is. CORA states neither this nor that the points lie on the boundary; the
polygon is an inner approximation, not an enclosure.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
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
  -- CORA's support point `q + Q l / √(lᵀ Q l)` is `q + G (v / ‖v‖₂)`, `v = Gᵀ l`
  set v : Vec ℝ 2 := E.Gᵀ *ᵥ L[i] with hv
  have hpt : E.q + (Real.sqrt (L[i] ⬝ᵥ E.Q *ᵥ L[i]))⁻¹ • (E.Q *ᵥ L[i])
      = E.q + E.G *ᵥ (‖v‖₂⁻¹ • v) := by
    rw [Matrix.mulVec_smul, hv, Matrix.mulVec_mulVec, E.G_mul_transpose, Ellipsoid.quad_eq,
      dotProduct_self, Real.sqrt_sq (norm₂_nonneg _)]
  show E.q + (Real.sqrt (L[i] ⬝ᵥ E.Q *ᵥ L[i]))⁻¹ • (E.Q *ᵥ L[i]) ∈ E.construct
  rw [hpt]
  -- the factor `‖v‖⁻¹ • v` has length at most one
  refine E.mem_construct ?_
  rw [norm₂_smul, abs_of_nonneg (inv_nonneg.mpr (norm₂_nonneg v))]
  rcases (norm₂_nonneg v).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [inv_mul_cancel₀ h.ne']

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
