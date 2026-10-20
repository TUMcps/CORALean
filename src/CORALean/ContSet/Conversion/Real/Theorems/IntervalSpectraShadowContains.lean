module

public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeSpectraShadowExact
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow

@[expose] public section

/-!
# A box as a spectrahedral shadow

Through the zonotope, which loses nothing either time: a box is a zonotope with
axis-aligned generators, and a zonotope is a spectrahedral shadow.

Only the enclosing direction is stated, for `Interval.zonotope`'s reason: a box
whose `sup` falls below its `inf` denotes nothing, while the set built from it
denotes the box with the two swapped.

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* interval is contained in its spectrahedral shadow
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.spectraShadow_contains (I : Interval (Vec ℝ n)) :
    I.construct ⊆ I.spectraShadow.construct :=
  subset_trans I.zonotope_contains (Zonotope.spectraShadow_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
