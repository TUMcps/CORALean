import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
import CORALean.ContSet.Zonotope.Float.Operations.MatPlusInterval

/-!
# `GZonotope.matPlusInterval` over-approximates the sum

Reassociation and `matPlus_outer`: the interval's point joins the box's.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GZonotope.matPlusInterval_outer (Z : GZonotope (Mat 𝕋 m n)) (I : Interval (Mat 𝕋 m n)) :
    Z.construct + I.construct ⊆ (GZonotope.matPlusInterval Z I).construct := by
  rintro _ ⟨_, ⟨a, ha, e, he, rfl⟩, x, hx, rfl⟩
  refine ⟨a, ha, e + x, Interval.matPlus_outer _ _ he hx, ?_⟩
  show a + (e + x) = a + e + x
  abel

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
