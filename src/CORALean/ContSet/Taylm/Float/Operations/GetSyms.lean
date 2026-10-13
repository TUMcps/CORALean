module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Taylm.Real.Operations.GetSyms

@[expose] public section

/-!
# `Taylm.getSyms`, over a floating-point scalar

The polynomial part of the stored model without its remainder, as a function of the variables: the
stored floats read as exact coefficients (`nominal`), evaluated at a real point. CORA's `sym`
expression and its variable names are not modelled. Nothing is rounded here: the function is the
stored polynomial itself, and the model's remainder is what `getSyms_mem` adds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.getSyms (T : Taylm 𝕋 n) (t : Vec ℝ n) : ℝ := T.nominal.getSyms t

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
