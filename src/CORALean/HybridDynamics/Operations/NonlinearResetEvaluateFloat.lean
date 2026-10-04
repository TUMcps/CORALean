import CORALean.HybridDynamics.Definitions.NonlinearResetFloatModel

/-!
# `NonlinearReset.evaluate` over boxes

CORA's `nonlinearReset/evaluate` at a box of pre-jump states and a box of inputs: the float
model's interval extension of the reset, in directed rounding. Soundness is
`evaluate_mem_evaluateFloat`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


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
