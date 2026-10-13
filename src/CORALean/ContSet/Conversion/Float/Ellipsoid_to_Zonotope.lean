import CORALean.ContSet.Conversion.Float.Ellipsoid_to_Interval
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope

/-!
# An ellipsoid as a zonotope, over a floating-point scalar

Through the box, as in the exact layer, so the same certificate `s` of one
proposed length per coordinate is carried: the box touches the ellipsoid on
every face up to what `s` was worth, and the box-to-zonotope step adds only
rounding outward.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def Ellipsoid.zonotope (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n) : Zonotope (Vec 𝕋 n) :=
  (E.interval s).zonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.zonotope_contains (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n)
    (hs : ∀ i, toReal (sqSumUp fun j => absolute (E.G i j))
      ≤ toReal (mulDown (s i) (s i))) :
    E.construct ⊆ (E.zonotope s).construct :=
  subset_trans (E.interval_contains s hs) (Interval.zonotope_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
