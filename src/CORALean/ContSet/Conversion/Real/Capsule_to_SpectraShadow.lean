import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_SpectraShadow

/-!
# A capsule as a spectrahedral shadow

Via the bounding box: `Capsule.interval`, then the box's own conversion. An outer enclosure,
coarser than CORA's conversion. CORA's `spectraShadow(capsule)` is the exact sum of the
segment's and the ball's spectrahedral shadows. Here the capsule is first replaced by its axis-
aligned box, which loses the rounded ends and the slant of the segment.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Capsule.spectraShadow (C : Capsule n) : SpectraShadow (Vec ℝ n) :=
  C.interval.spectraShadow


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.spectraShadow_contains (C : Capsule n) :
    C.construct ⊆ C.spectraShadow.construct :=
  subset_trans C.interval_contains (Interval.spectraShadow_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
