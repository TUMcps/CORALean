import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `PolyZonotope.centre`

CORA's `center` for a polynomial zonotope returns the field `c`: the stored centre,
unchanged. It carries no guarantee of its own; `centre_mem_construct` says when it lies in
the set.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.centre (pZ : PolyZonotope 𝕋 n) : Vec 𝕋 n := pZ.c

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
