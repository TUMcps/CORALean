import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
import CORALean.Global.Partition

/-!
# `ConPolyZono.dropRadius`

How far the dropped generators of both blocks reach in each coordinate. A
monomial and an independent coefficient obey the same bound, so one box
covers the two blocks together.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n d r dI rI : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far the dropped generators of both blocks reach in each coordinate. A
monomial and an independent coefficient obey the same bound, so one box covers
the two blocks together. -/
def ConPolyZono.dropRadius (C : ConPolyZono (Vec ℝ n))
    (partD : Split (Fin C.h) into (Fin d) and (Fin r))
    (partI : Split (Fin C.q) into (Fin dI) and (Fin rI)) : Vec ℝ n :=
  fun i => (∑ l, |C.G (partD.right l) i|) + ∑ j, |C.GI (partI.right j) i|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
