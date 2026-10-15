module

public import CORALean.ContSet.Conversion.Float.Theorems.EllipsoidIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalPolyZonotopeContains
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# An ellipsoid as a polynomial zonotope, over a floating-point scalar

Through the box, certificate `s` carried as for `Ellipsoid.interval`, then the
box's exact polynomial zonotope.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.polyZonotope_contains (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n)
    (hs : ∀ i, toReal (E.Q i i) ≤ toReal (mulDown (s i) (s i))) :
    E.construct ⊆ (E.polyZonotope s).construct :=
  subset_trans (E.interval_contains s hs) (Interval.polyZonotope_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
