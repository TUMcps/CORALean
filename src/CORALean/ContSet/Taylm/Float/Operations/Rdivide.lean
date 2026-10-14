module

public import CORALean.ContSet.Taylm.Float.Operations.Inv

@[expose] public section

/-!
# `Taylm.rdivide`, over a floating-point scalar

A model over a model, CORA's `priv_inverse` then `times`: `T₁ · (1/T₂)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.rdivide (T₁ T₂ : Taylm 𝕋 n) : Taylm 𝕋 n := T₁.times T₂.inv

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
