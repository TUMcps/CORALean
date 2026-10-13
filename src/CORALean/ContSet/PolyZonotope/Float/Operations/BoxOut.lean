module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import Mathlib.Data.Finset.Sort
public import CORALean.ContSet.PolyZonotope.Float.Operations.BoxOutRadius

@[expose] public section

/-!
# `PolyZonotope.boxOut`, over a floating-point scalar

The tail of CORA's `outerApprox`: the `removed` dependent generators leave `G` and `E` for a
diagonal box appended to the independent block, which also covers the `taken` independent ones.
The radius is `boxOutRadius`, at least the exact one; centre, error box and the kept columns are
copied, the kept columns being read off in order by `orderEmbOfFin`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `pZ` without the `removed` dependent generators, and the box of those and of the `taken`
independent ones appended to the independent block. -/
def PolyZonotope.boxOut (pZ : PolyZonotope (Vec 𝕋 n)) (removed : Fin pZ.h → Bool)
    (taken : Fin pZ.q → Bool) : PolyZonotope (Vec 𝕋 n) where
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
