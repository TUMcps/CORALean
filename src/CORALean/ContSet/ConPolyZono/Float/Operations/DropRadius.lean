module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.dropRadius`, over a floating-point scalar

Split out of `Reduce.lean` (issue #62): read again by `Theorems/
ReduceByOuter.lean`, outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d r dI rI : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far the dropped generators of both blocks reach in each coordinate: the
two row sums, added upward. A monomial and an independent coefficient obey the
same bound, so one box covers the two blocks together. -/
def ConPolyZono.dropRadius (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (partD : Split (Fin cPZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin cPZ.q) into (Fin dI) ⊕ (Fin rI)) : Vec 𝕋 n :=
  fun i₀ => addUp (radius (fun i l => cPZ.G (partD.right l) i) i₀)
    (radius (fun i j => cPZ.GI (partI.right j) i) i₀)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
