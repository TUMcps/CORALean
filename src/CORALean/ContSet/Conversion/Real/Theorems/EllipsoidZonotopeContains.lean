module

public import CORALean.ContSet.Conversion.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Zonotope.Real.Theorems.SqNormLeMaxNormSq
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# An ellipsoid as a zonotope

Through the box, as everything reaching a zonotope does here: a tighter
zonotope enclosure of an ellipsoid is a fitting problem — how many generators,
pointed which way — rather than a conversion, and CORA leaves that choice to the
caller too.

The box step is tight and the box-to-zonotope step is exact, so all the loss is
in the first, and it is the loss of an axis-aligned enclosure of a rotated set.

CORA's `'inner:norm'` and `'outer:norm'` are [1, Thm. 2] and [1, Thm. 4]: points `S` on the unit
sphere, ideally spread evenly ([1, Lemma 4]), scaled by the inverse of a bound on the maximum,
or below the minimum, norm of `Z(S, 0)` and mapped by the ellipsoid's generator.
`zonotopeInnerNorm` and `zonotopeNorm` take `S` and the bound; the guarantees hold for any `S`.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.zonotope_contains (E : Ellipsoid n) : E.construct ⊆ E.zonotope.construct :=
  subset_trans E.interval_contains (Interval.zonotope_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
