import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.InflatedContSet.InflatedContSet
import CORALean.ContSet.Interval.Real.Theorems.Convex

/-!
# An inflated representation of a convex set is convex

A nominal set plus an error box, and `Convex.add` carries the property across
a Minkowski sum: the nominal part is convex by hypothesis and the box because
its coordinates are bounded independently. So the error box costs convexity
nothing, whatever representation the nominal part is.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.InflatedContSet

open Pointwise

variable {𝕋 S N : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable [ContSet N (Vec ℝ n)] [InflatedContSet S N (Vec 𝕋 n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem convex_construct [ConvexSet N (Vec ℝ n)] (s : S) : Convex ℝ (construct s) :=
  Convex.add (ConvexSet.convex_construct (nominal s)) (error s).nominal.convex_construct

end CORALean.Float.InflatedContSet


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
