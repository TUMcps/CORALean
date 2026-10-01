import CORALean.ContSet.Interval.Float.Operations.ConvHull
import CORALean.ContSet.Interval.Float.Theorems.OrOuter
import CORALean.ContSet.Interval.Real.Theorems.Convex

/-!
# `Interval.convHull` contains the convex hull of the union

A box is convex, so it contains the convex hull of whatever the union of two boxes lies in.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.convHull_outer (I₁ I₂ : Interval (Vec 𝕋 n)) :
    convexHull ℝ (I₁.construct ∪ I₂.construct) ⊆ (I₁.convHull I₂).construct :=
  convexHull_min (Interval.or_outer I₁ I₂) (Real.Interval.convex_construct _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
