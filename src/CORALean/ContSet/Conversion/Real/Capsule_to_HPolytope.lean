import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_HPolytope

/-!
# A capsule as a halfspace description

Via the bounding box: `Capsule.interval`, then the box's own conversion. An outer enclosure,
coarser than CORA's conversion. CORA's `polytope(capsule)` is exact for a point and a line, and
for a ball-thickened segment outer-approximates through the support function in a set of
directions. Here the capsule is first replaced by its axis-aligned box, which loses the rounded
ends and the slant of the segment.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Capsule.hPolytope (C : Capsule n) : HPolytope (Vec ℝ n) :=
  C.interval.hPolytope


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.hPolytope_contains (C : Capsule n) :
    C.construct ⊆ C.hPolytope.construct :=
  subset_trans C.interval_contains (Interval.hPolytope_exact _).symm.subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
