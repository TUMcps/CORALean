import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `PolyZonotope.centre`

CORA's `center` for a polynomial zonotope returns the field `c`: the stored centre,
unchanged. It carries no guarantee of its own; `centre_mem_construct` says when it lies in
the set.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.centre (pZ : PolyZonotope (Vec 𝕋 n)) : Vec 𝕋 n := pZ.c

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
