import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
import CORALean.Global.Partition

/-!
# How far the generators `reduceBy` drops can reach

Split out of `Reduce.lean` (issue #62): read again by the float layer's own
`reduceBy` and by `Theorems/AbsDroppedLeDropRadius.lean`, both outside this
file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- How far the dropped generators of both blocks reach in each coordinate. A
monomial and an independent coefficient obey the same bound, so one box covers
the two blocks together. -/
def PolyZonotope.dropRadius (PZ : PolyZonotope (Vec ℝ n)) {d r dI rI : ℕ}
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r))
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) : Vec ℝ n :=
  fun i => (∑ l, |PZ.G (partD.right l) i|) + ∑ j, |PZ.GI (partI.right j) i|

end CORALean.Real
