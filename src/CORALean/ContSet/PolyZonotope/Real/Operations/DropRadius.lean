module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# How far the generators `reduceBy` drops can reach

Split out of `Reduce.lean` (issue #62): read again by the float layer's own
`reduceBy` and by `Theorems/AbsDroppedLeDropRadius.lean`, both outside this
file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far the dropped generators of both blocks reach in each coordinate. A
monomial and an independent coefficient obey the same bound, so one box covers
the two blocks together. -/
def PolyZonotope.dropRadius (pZ : PolyZonotope (Vec ℝ n)) {d r dI rI : ℕ}
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) : Vec ℝ n :=
  fun i => (∑ l, |pZ.G (partD.right l) i|) + ∑ j, |pZ.GI (partI.right j) i|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
