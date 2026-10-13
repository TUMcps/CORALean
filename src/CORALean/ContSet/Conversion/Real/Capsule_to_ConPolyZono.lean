module

public import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_ConPolyZono

@[expose] public section

/-!
# A capsule as a constrained polynomial zonotope

Via the bounding box: `Capsule.interval`, then the box's own conversion. An outer enclosure,
coarser than CORA's conversion. CORA's `conPolyZono(capsule)` is the exact sum of the segment
and the ball's constrained polynomial zonotope. Here the capsule is first replaced by its axis-
aligned box, which loses the rounded ends and the slant of the segment.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Capsule.conPolyZono (C : Capsule n) : ConPolyZono (Vec ℝ n) :=
  C.interval.conPolyZono


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.conPolyZono_contains (C : Capsule n) :
    C.construct ⊆ C.conPolyZono.construct :=
  subset_trans C.interval_contains (Interval.conPolyZono_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
