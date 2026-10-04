import CORALean.ContSet.Taylm.Float.Operations.TermBoxBounds
import CORALean.Global.Float.ListSum

/-!
# `Taylm.polyBoxBounds`, over a floating-point scalar

The range of a term list over a box `B`: the term ranges summed, each end rounded outward.
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

def Taylm.polyBoxBounds (L : List (𝕋 × (Fin n → ℕ))) (B : Fin n → 𝕋 × 𝕋) : 𝕋 × 𝕋 :=
  (listSumDown (L.map fun a => (Taylm.termBoxBounds B a).1),
    listSumUp (L.map fun a => (Taylm.termBoxBounds B a).2))
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
