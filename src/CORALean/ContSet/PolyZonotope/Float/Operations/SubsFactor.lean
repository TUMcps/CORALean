module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.subsFactor`

The factor of the result that `pZin`'s factor `j` is: `pZ`'s own where the identifiers are shared,
else a new one after `pZ`'s.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.subsFactor (pZ : PolyZonotope (Vec 𝕋 n)) {nu : ℕ} (pZin : PolyZonotope (Vec 𝕋 nu))
    (share : Fin pZin.p → Option (Fin pZ.p)) (j : Fin pZin.p) : Fin (pZ.p + pZin.p) :=
  match share j with
  | some k => Fin.castAdd pZin.p k
  | none => Fin.natAdd pZ.p j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
