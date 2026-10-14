module

public import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Capsule_to_PolyZonotope

@[expose] public section

/-!
# A capsule as a polynomial zonotope

Via the bounding box: `Capsule.interval`, then the box's own conversion. An outer enclosure,
coarser than CORA's conversion. CORA's `polyZonotope(capsule)` parametrizes the ball by Taylor
models of the spherical angles and linearly combines the two end balls. Here the capsule is
first replaced by its axis-aligned box, which loses the rounded ends and the slant of the
segment.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.polyZonotope_contains (C : Capsule n) :
    C.construct ⊆ C.polyZonotope.construct :=
  subset_trans C.interval_contains (Interval.polyZonotope_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
