import CORALean.ContSet.Interval.Float.Operations.Or

/-!
# `Interval.convHull`

CORA's `convHull_` ends in `I | S`, so it is `or`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.convHull (I₁ I₂ : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) := I₁.or I₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
