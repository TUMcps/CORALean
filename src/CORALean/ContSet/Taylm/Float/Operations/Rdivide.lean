import CORALean.ContSet.Taylm.Float.Operations.Times
import CORALean.ContSet.Taylm.Float.Operations.Inv

/-!
# `Taylm.rdivide`, over a floating-point scalar

A model over a model, CORA's `priv_inverse` then `times`: `T₁ · (1/T₂)`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.rdivide (T₁ T₂ : Taylm 𝕋 n) : Taylm 𝕋 n := T₁.times T₂.inv

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
