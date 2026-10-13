module

public import CORALean.ContSet.Taylm.Float.Operations.ProdBounds

@[expose] public section

/-!
# `Taylm.termBoxBounds`, over a floating-point scalar

The range of one term `c ∏ tₖ ^ eₖ` over a box `B`: the power ranges of the coordinates
multiplied, then the coefficient, every end rounded outward.
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

def Taylm.termBoxBounds (B : Fin n → 𝕋 × 𝕋) (a : 𝕋 × (Fin n → ℕ)) : 𝕋 × 𝕋 :=
  let M := Taylm.prodBounds fun k => Taylm.powBounds (B k).1 (B k).2 (a.2 k)
  (Interval.mulLo a.1 a.1 M.1 M.2, Interval.mulHi a.1 a.1 M.1 M.2)
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
