import CORALean.ContSet.Polygon.Real.Theorems.SampledHullMissesCircle
import CORALean.ContSet.Polygon.Real.Operations.OverlapsRegionCora
import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# CORA's `polygon/isIntersecting_` misses an ellipsoid it intersects

`@polygon/isIntersecting_.m` l. 49 replaces an ellipsoid operand by `polygon(S)`, an inner
approximation built from boundary samples (`@ellipsoid/polygon.m`). For the unit disk `E` and any
finite boundary sample `V`, a boundary point `z` of `E` lies outside the sampled polygon, hence so
does a small square `P` about `z`: `P` meets `E` at `z`, yet `overlaps(P, polygon(E))` is false and
CORA returns false. `contSet/isIntersecting.m` l. 38 reorders by precedence (polygon 15,
ellipsoid 50) and calls the polygon method. Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A square `P = closedBall z δ` (the supremum-norm ball) meets the unit disk, but CORA's test
against `polygon(E)` says it does not. -/
theorem Polygon.isIntersectingEllipsoid_cora_counterexample (V : Set (Vec ℝ 2)) (hV : V.Finite)
    (hc : ∀ p ∈ V, p 0 ^ 2 + p 1 ^ 2 = 1) :
    ∃ (z : Vec ℝ 2) (δ : ℝ), 0 < δ ∧
      ¬ Polygon.overlapsRegionCora (Metric.closedBall z δ) (Polygon.sampledHullCora V) ∧
      (Metric.closedBall z δ ∩ (⟨2, 0, 1⟩ : Ellipsoid 2).construct).Nonempty := by -- --- PROOF ---
  obtain ⟨z, hz, hzn⟩ := Polygon.exists_circle_notMem_sampledHull V hV hc
  have hclosed : IsClosed (Polygon.sampledHullCora V) := (hV.isCompact_convexHull ℝ).isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl z hzn
  refine ⟨z, ε / 2, by positivity, fun ⟨x, hxP, hxH⟩ => ?_,
    ⟨z, Metric.mem_closedBall_self (by positivity), z, ?_, by simp⟩⟩
  -- the square is inside the ball `ε` about `z` that misses the closed hull
  · exact hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hxP) (by linarith)) hxH
  · show Real.sqrt (∑ i, z i ^ 2) ≤ 1
    rw [Fin.sum_univ_two, hz]
    simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
