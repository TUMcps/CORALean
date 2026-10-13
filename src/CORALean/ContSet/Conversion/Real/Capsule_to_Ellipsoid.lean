import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_Ellipsoid

/-!
# A capsule as an ellipsoid

Via the bounding box: `Capsule.interval`, then the box's own conversion. An outer enclosure,
coarser than CORA's conversion. CORA's `ellipsoid(capsule)` is exact for a ball, and otherwise
outer-approximates the union of the two end balls by a semidefinite program. Here the capsule
is first replaced by its axis-aligned box, which loses the rounded ends and the slant of the
segment.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Capsule.ellipsoid (C : Capsule n) : Ellipsoid n :=
  C.interval.ellipsoid


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.ellipsoid_contains (C : Capsule n) :
    C.construct ⊆ C.ellipsoid.construct :=
  subset_trans C.interval_contains (Interval.ellipsoid_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
