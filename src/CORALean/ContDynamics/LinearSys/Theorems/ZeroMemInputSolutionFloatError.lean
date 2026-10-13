import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
import CORALean.ContDynamics.LinearSys.Theorems.ZeroMemInputTaylorSumFloatError
import CORALean.ContDynamics.LinearSys.Theorems.ZeroMemIntervalInputRemainder

/-!
# `inputSolutionFloat` keeps the origin in its error box

The Taylor sum does (`zero_mem_inputTaylorSumFloat_error`), the remainder
product does because its interval holds the zero matrix
(`zero_mem_intervalInputRemainder`), and so does their float sum. What the
float step's upper bound asks of its input set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `inputSolutionFloat` keeps `0` in its error box, given `U` has it, at `r ≥ 0` and an
admissible order. -/
theorem LinearSys.zero_mem_inputSolutionFloat_error (sys : LinearSys 𝕋 n) {r : 𝕋}
    (hr : 0 ≤ toReal r) {η : ℕ} (hη : sys.OrderAdmissibleFloat r r η) {U : Zonotope (Vec 𝕋 n)}
    (hU : (0 : Vec ℝ n) ∈ U.E.construct) :
    (0 : Vec ℝ n) ∈ (sys.inputSolutionFloat r η U).E.construct := by -- --- PROOF ---
  show (0 : Vec ℝ n) ∈ ((Zonotope.plus _ _).materialise).E.construct
  rw [Zonotope.materialise_eq]
  refine Zonotope.zero_mem_plus_error (sys.zero_mem_inputTaylorSumFloat_error hr hU η) ?_
  show (0 : Vec ℝ n) ∈ ((Zonotope.mtimesIntervalMat _ U).materialise).E.construct
  rw [Zonotope.materialise_eq]
  exact Zonotope.zero_mem_mtimesIntervalMat_error (sys.zero_mem_intervalInputRemainder hr hη) hU

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
