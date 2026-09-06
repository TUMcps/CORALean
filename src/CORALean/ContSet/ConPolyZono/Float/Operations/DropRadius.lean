import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.Global.Partition

/-!
# `ConPolyZono.dropRadius`, over a floating-point scalar

Split out of `Reduce.lean` (issue #62): read again by `Theorems/
ReduceByOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d r dI rI : ℕ}

/-- How far the dropped generators of both blocks reach in each coordinate: the
two row sums, added upward. A monomial and an independent coefficient obey the
same bound, so one box covers the two blocks together. -/
def ConPolyZono.dropRadius (C : ConPolyZono 𝕋 n)
    (partD : Split (Fin C.h) into (Fin d) and (Fin r))
    (partI : Split (Fin C.q) into (Fin dI) and (Fin rI)) : Vec 𝕋 n :=
  fun i₀ => addUp (radius (fun i l => C.G i (partD.right l)) i₀)
    (radius (fun i j => C.GI i (partI.right j)) i₀)

end CORALean.Float
