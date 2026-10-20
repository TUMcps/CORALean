module

public import CORALean.ContSet.Polygon.Real.Operations.RegionCenter
public import CORALean.ContSet.Polygon.Real.Theorems.IsCompact
public import Mathlib.Analysis.Convex.Integral

@[expose] public section

/-!
# `Polygon.regionCenter` lies in every closed convex set holding the region

The centroid of a compact region of positive area is in its convex hull (an average of points of
the region), hence in the hull of the polygon's vertices (`Polygon.convexHull_vertices`) and in
every convex set that holds the region. The centroid itself is not computed; for a convex region
it lies in the region, for a non-convex one (an L-shape, a ring) it may lie outside.

## Inputs
* `S` – set of points
* `C` – set of points

## Hypotheses
* `hS` – `IsCompact S`
* `hC` – `Convex ℝ C`
* `hCc` – `IsClosed C`
* `hSC` – `S ⊆ C`
* `h0` – `S` has nonzero volume

## Conclusion
* `Polygon.regionCenter` lies in every closed convex set holding the region
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.regionCenter_mem {S C : Set (Vec ℝ 2)} (hS : IsCompact S) (hC : Convex ℝ C)
    (hCc : IsClosed C) (hSC : S ⊆ C) (h0 : MeasureTheory.volume S ≠ 0) :
    Polygon.regionCenter S ∈ C := by -- --- PROOF ---
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict S) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hS.measure_lt_top⟩
  haveI : NeZero (MeasureTheory.volume.restrict S) := ⟨by
    intro h
    apply h0
    have := congrArg (fun μ : Measure (Vec ℝ 2) => μ Set.univ) h
    simpa [Measure.restrict_apply_univ] using this⟩
  refine hC.average_mem hCc ?_ ?_
  · filter_upwards [ae_restrict_mem hS.measurableSet] with x hx using hSC hx
  · exact (continuous_id.continuousOn.integrableOn_compact hS)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
