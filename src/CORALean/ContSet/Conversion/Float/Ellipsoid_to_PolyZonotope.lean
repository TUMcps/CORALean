module

public import CORALean.ContSet.Conversion.Float.Ellipsoid_to_Interval
public import CORALean.ContSet.Conversion.Float.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Ellipsoid_to_PolyZonotope

@[expose] public section

/-!
# An ellipsoid as a polynomial zonotope, over a floating-point scalar

Through the box, certificate `s` carried as for `Ellipsoid.interval`, then the
box's exact polynomial zonotope.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.polyZonotope_contains (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n)
    (hs : ∀ i, toReal (sqSumUp fun j => absolute (E.G i j))
      ≤ toReal (mulDown (s i) (s i))) :
    E.construct ⊆ (E.polyZonotope s).construct :=
  subset_trans (E.interval_contains s hs) (Interval.polyZonotope_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
