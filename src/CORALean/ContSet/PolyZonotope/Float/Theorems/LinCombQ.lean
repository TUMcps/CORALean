import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb

/-!
# `linComb`'s independent generator count is the sum of the two incoming ones

No fresh independent factor: the segment's own coefficient is dependent.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem PolyZonotope.linComb_q (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    (PZ₁.linComb PZ₂).q = PZ₁.q + PZ₂.q := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
