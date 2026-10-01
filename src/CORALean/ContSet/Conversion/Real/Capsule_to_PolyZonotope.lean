import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope

/-!
# A capsule as a polynomial zonotope

Via the bounding box: `Capsule.interval`, then the box's own conversion. An outer enclosure,
coarser than CORA's conversion. CORA's `polyZonotope(capsule)` parametrizes the ball by Taylor
models of the spherical angles and linearly combines the two end balls. Here the capsule is
first replaced by its axis-aligned box, which loses the rounded ends and the slant of the
segment.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Capsule.polyZonotope (C : Capsule n) : PolyZonotope (Vec ℝ n) :=
  C.interval.polyZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.polyZonotope_contains (C : Capsule n) :
    C.construct ⊆ C.polyZonotope.construct :=
  subset_trans C.interval_contains (Interval.polyZonotope_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
