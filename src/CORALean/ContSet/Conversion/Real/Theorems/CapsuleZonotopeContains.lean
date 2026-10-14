module

public import CORALean.ContSet.Conversion.Real.Theorems.CapsuleIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# A capsule as a zonotope

Via the bounding box: `Capsule.interval`, then the box's own conversion. An outer enclosure,
coarser than CORA's conversion. CORA's `zonotope(capsule)` adds a zonotope enclosure of the
ball (`order * n - 1` generators) to the segment's own generator, so it keeps the segment
exact. Here the capsule is first replaced by its axis-aligned box, which loses the rounded ends
and the slant of the segment.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.zonotope_contains (C : Capsule n) :
    C.construct ⊆ C.zonotope.construct :=
  subset_trans C.interval_contains (Interval.zonotope_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
