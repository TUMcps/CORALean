import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope

/-!
# A capsule as a vertex description

Via the bounding box: `Capsule.interval`, then the box's own conversion. An outer enclosure,
coarser than CORA's conversion. CORA has no capsule-to-vertex conversion: its
`polytope(capsule)` is a halfspace description. Here the capsule is first replaced by its axis-
aligned box, which loses the rounded ends and the slant of the segment.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Capsule.vPolytope (C : Capsule n) : VPolytope (Vec ℝ n) :=
  C.interval.vPolytope


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.vPolytope_contains (C : Capsule n) :
    C.construct ⊆ C.vPolytope.construct :=
  subset_trans C.interval_contains (Interval.vPolytope_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
