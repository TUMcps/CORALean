import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce

/-!
# `reduceBy`'s dependent generator count is the kept block's size
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d r dI rI : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
@[simp] theorem PolyZonotope.reduceBy_h (PZ : PolyZonotope 𝕋 n)
    (partD : Split (Fin PZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin PZ.q) into (Fin dI) ⊕ (Fin rI)) :
    (PZ.reduceBy partD partI).h = d := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
