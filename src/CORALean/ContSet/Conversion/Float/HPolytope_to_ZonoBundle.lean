import CORALean.ContSet.Conversion.Float.HPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_ZonoBundle

/-!
# A halfspace description as a bundle of one, over a floating-point scalar

Through the zonotope the box gives, then `Zonotope.zonoBundle`, exact. All the
loss is the box route's; the caller supplies the coordinate bounds.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 n}

def HPolytope.zonoBundle (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : ZonoBundle 𝕋 n :=
  (HPolytope.zonotope up lo).zonoBundle


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.zonoBundle_contains (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.zonoBundle up lo).construct :=
  subset_trans (HPolytope.zonotope_contains up lo) (Zonotope.zonoBundle_exact _).subset

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
