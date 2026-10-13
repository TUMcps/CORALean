import CORALean.ContSet.Polygon.Float.Theorems.IntervalContains
import CORALean.ContSet.Polygon.Float.Theorems.IsCompact
import CORALean.ContSet.Polygon.Real.Theorems.RegionCenterMem
import CORALean.ContSet.Interval.Real.Theorems.Convex
import CORALean.ContSet.Interval.Real.Theorems.IsClosed

/-!
# The centroid of a float polygon lies in its interval hull

CORA's `polygon/center` for a float polygon: the centroid of the region the float polygon denotes
(`Polygon.regionCenter`, the real average) lies in the box `Polygon.interval` computes, since the
box is convex and holds the region. A box, not the point; the area must be positive.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.center_mem_interval (P : Polygon 𝕋)
    (h0 : MeasureTheory.volume (ContSet.construct P) ≠ 0) :
    Real.Polygon.regionCenter (ContSet.construct P) ∈ (Polygon.interval P).construct :=
  Real.Polygon.regionCenter_mem (Polygon.isCompact_construct P)
    (Real.Interval.convex_construct _) (Real.Interval.isClosed_construct _)
    (Polygon.interval_contains P) h0

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
