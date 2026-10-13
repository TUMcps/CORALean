module

public import CORALean.HybridDynamics.Definitions.NonlinearResetFloatModel

@[expose] public section

/-!
# `NonlinearReset.evaluate` over boxes

CORA's `nonlinearReset/evaluate` at a box of pre-jump states and a box of inputs: the float
model's interval extension of the reset, in directed rounding. Soundness is
`evaluate_mem_evaluateFloat`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reset over the boxes `X` and `U`. -/
def NonlinearReset.FloatModel.evaluateFloat (fm : NonlinearReset.FloatModel 𝕋 n m p)
    (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) : Interval (Vec 𝕋 p) :=
  fm.f X U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
