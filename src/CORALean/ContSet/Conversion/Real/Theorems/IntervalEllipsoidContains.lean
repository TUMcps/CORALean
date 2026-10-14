module

public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeEllipsoidContains
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A box as an ellipsoid

Through the zonotope, which loses nothing: a box is a zonotope with `n`
axis-aligned generators, so what comes out is the centre with generator matrix
`√n · diag(radius)` — the smallest ellipsoid containing the box, `√n` times the
inscribed one, and the classical bound is met rather than approached.

Only the enclosing direction, for the same reason `Interval_to_Zonotope` gives
only that one: a box whose `sup` falls below its `inf` denotes nothing while the
ellipsoid built from it denotes the box with the two swapped.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.ellipsoid_contains (I : Interval (Vec ℝ n)) :
    I.construct ⊆ I.ellipsoid.construct :=
  subset_trans I.zonotope_contains (Zonotope.ellipsoid_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
