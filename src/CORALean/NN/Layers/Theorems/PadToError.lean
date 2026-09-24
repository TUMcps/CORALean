import CORALean.NN.Layers.Operations.PolyRelaxationPadTo

/-!
# Padding leaves the error alone

By `rfl`, which is what makes it free.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyRelaxation.padTo_error (P : PolyRelaxation 𝕋 k) (M : ℕ) :
    (P.padTo M).error = P.error := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
