import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.Global.Partition

/-!
# How far the generators `reduceBy` drops can reach, over a floating-point scalar

Split out of `Reduce.lean` (issue #62): read again by `reduceBy` in this
directory, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d r dI rI : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far the dropped generators of both blocks reach in each coordinate: the
two row sums, added upward. A monomial and an independent coefficient obey the
same bound, so one box covers the two blocks together. -/
def PolyZonotope.dropRadius (pZ : PolyZonotope 𝕋 n)
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) : Vec 𝕋 n :=
  fun i₀ => addUp (radius (fun i l => pZ.G (partD.right l) i) i₀)
    (radius (fun i j => pZ.GI (partI.right j) i) i₀)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
