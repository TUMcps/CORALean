module

public import CORALean.ContSet.Taylm.Float.Operations.TermBounds
public import CORALean.Global.Float.ListSum

@[expose] public section

/-!
# The range of a term list over the box

The term ranges summed, each end rounded outward.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.polyBounds (L : List (𝕋 × (Fin n → ℕ))) : 𝕋 × 𝕋 :=
  (listSumDown (L.map fun a => (Taylm.termBounds a).1),
    listSumUp (L.map fun a => (Taylm.termBounds a).2))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
