import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Interval_to_Capsule

/-!
# A zonotope as a capsule, over a floating-point scalar

CORA's `capsule(zonotope)` with the SVD basis taken as the identity: the capsule of
`interval(Z)` (`Zonotope.interval`, then `Interval.capsule`, `k` Newton steps for the roots). An
outer enclosure, as over ℝ; it is not CORA's rotated capsule.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def Zonotope.capsule (k : ℕ) (Z : Zonotope (Vec 𝕋 n)) : Capsule 𝕋 n :=
  Z.interval.capsule k


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.capsule_contains (k : ℕ) (Z : Zonotope (Vec 𝕋 n)) :
    Z.construct ⊆ (Z.capsule k).construct :=
  subset_trans Z.interval_contains (Z.interval.capsule_contains k)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
