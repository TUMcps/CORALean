import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import Mathlib.Data.Finset.Sort
import CORALean.ContSet.PolyZonotope.Float.Operations.BoxOutRadius

/-!
# `PolyZonotope.boxOut`, over a floating-point scalar

The tail of CORA's `outerApprox`: the `removed` dependent generators leave `G` and `E` for a
diagonal box appended to the independent block, which also covers the `taken` independent ones.
The radius is `boxOutRadius`, at least the exact one; centre, error box and the kept columns are
copied, the kept columns being read off in order by `orderEmbOfFin`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `pZ` without the `removed` dependent generators, and the box of those and of the `taken`
independent ones appended to the independent block. -/
def PolyZonotope.boxOut (pZ : PolyZonotope 𝕋 n) (removed : Fin pZ.h → Bool)
    (taken : Fin pZ.q → Bool) : PolyZonotope 𝕋 n where
  p := pZ.p
  h := (Finset.univ.filter fun l => removed l = false).card
  q := pZ.q + n
  c := pZ.c
  G := fun l => pZ.G ((Finset.univ.filter fun l => removed l = false).orderEmbOfFin rfl l)
  E := fun k l => pZ.E k ((Finset.univ.filter fun l => removed l = false).orderEmbOfFin rfl l)
  GI := Fin.append pZ.GI fun j i => diagonalBlock (pZ.boxOutRadius removed taken) i j
  err := pZ.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
