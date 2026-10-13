import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `PolyZonotope.noIndep` over a floating-point scalar

CORA's `noIndep`: `GI = zeros(n, 0)`, the independent generators dropped and nothing else
changed, the error box included. Nothing rounds. It is not `PolyZonotope.dependent`, which
turns the independent block into dependent generators and keeps the set: `noIndep` keeps
only what the dependent factors reach, a subset.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The independent block emptied. -/
def PolyZonotope.noIndep (pZ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) where
  p := pZ.p
  h := pZ.h
  q := 0
  c := pZ.c
  G := pZ.G
  E := pZ.E
  GI := Fin.elim0
  err := pZ.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
