import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
import CORALean.Global.Partition

/-!
# `ConPolyZono.dropRadius`

How far the dropped generators of both blocks reach in each coordinate. A
monomial and an independent coefficient obey the same bound, so one box
covers the two blocks together.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n d r dI rI : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far the dropped generators of both blocks reach in each coordinate. A
monomial and an independent coefficient obey the same bound, so one box covers
the two blocks together. -/
def ConPolyZono.dropRadius (cPZ : ConPolyZono (Vec ℝ n))
    (partD : Split (Fin cPZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin cPZ.q) into (Fin dI) ⊕ (Fin rI)) : Vec ℝ n :=
  fun i => (∑ l, |cPZ.G (partD.right l) i|) + ∑ j, |cPZ.GI (partI.right j) i|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
