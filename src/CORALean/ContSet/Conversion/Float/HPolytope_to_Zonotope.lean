import CORALean.ContSet.Conversion.Float.HPolytope_to_Interval
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope

/-!
# A halfspace description as a zonotope, over a floating-point scalar

Through its box, which is what the certificates give.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}

def HPolytope.zonotope (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : Zonotope (Vec 𝕋 n) :=
  (HPolytope.interval up lo).zonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.zonotope_contains (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.zonotope up lo).construct :=
  subset_trans (HPolytope.interval_contains up lo) (Interval.zonotope_contains _)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
