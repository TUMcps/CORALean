import CORALean.ContSet.Interval.Real.Operations.ConvHull
import CORALean.ContSet.Interval.Real.Theorems.OrOuter
import CORALean.ContSet.Interval.Real.Theorems.Convex
import Mathlib.Analysis.Convex.Hull

/-!
# `Interval.convHull` contains the convex hull of the union

A box is convex, so it contains the convex hull of whatever the union of two boxes lies in.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.convHull_outer (I₁ I₂ : Interval α) :
    convexHull ℝ (I₁.construct ∪ I₂.construct) ⊆ (I₁.convHull I₂).construct :=
  convexHull_min (Interval.or_outer I₁ I₂) (Interval.convex_construct _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
