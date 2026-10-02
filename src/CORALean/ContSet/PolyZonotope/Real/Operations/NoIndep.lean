import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.noIndep`

CORA's `@polyZonotope/noIndep`: `pZ.GI = zeros(dim(pZ), 0)`, the independent generators dropped and
nothing else changed. This is *not* `PolyZonotope.dependent`, which turns the independent block
into dependent generators (and denotes the same set): `noIndep` denotes the part of the set the
dependent factors reach alone, a subset (see `noIndep_construct`, `noIndep_subset`).
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `polyZonotope/noIndep`: the independent block emptied. -/
def PolyZonotope.noIndep (pZ : PolyZonotope α) : PolyZonotope α where
  p := pZ.p
  h := pZ.h
  q := 0
  c := pZ.c
  G := pZ.G
  E := pZ.E
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
