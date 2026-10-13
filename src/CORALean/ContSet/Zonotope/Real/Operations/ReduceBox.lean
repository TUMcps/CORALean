import CORALean.ContSet.Zonotope.Real.Operations.GirardSplit
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBox

/-!
# `Zonotope.reduceBox`

The error `reduce` pays, as a zonotope of its own: `reduceByBox` at the
partition Girard's rule picks. So `reduce Z o` reaches no further than `Z` plus
this, which is the reverse of `reduce_outer` and what an inner approximation
subtracts back off.

The second branch is not a formality. `reduce` leaves a zonotope already at
order `o` alone, and there is then no dropped generator to box; the origin is
the error it pays, and a set is contained in itself plus `{0}`. So the box is
`ofPoint 0` there rather than undefined, and the bound holds at every order.

Not a `Reduce` operation and no class instantiates it: `Reduce` obliges the
outer direction only, while a box for the reverse one is a fact about the
particular rule `reduce` runs.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box `reduce` absorbs the dropped generators into, on its own — and the
origin at an order already met, where nothing is dropped. -/
noncomputable def Zonotope.reduceBox (Z : Zonotope (Vec ℝ n)) (o : ℕ) : Zonotope (Vec ℝ n) :=
  if hlt : o * n < Z.h then Z.reduceByBox (Z.girardSplit o hlt) else Zonotope.ofPoint 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
