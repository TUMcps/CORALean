module

public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ZeroMemInputTaylorSumFloatError
public import CORALean.ContDynamics.LinearSys.Theorems.ZeroMemIntervalInputRemainder

@[expose] public section

/-!
# `inputSolutionFloat` keeps the origin in its error box

The Taylor sum does (`zero_mem_inputTaylorSumFloat_error`), the remainder
product does because its interval holds the zero matrix
(`zero_mem_intervalInputRemainder`), and so does their float sum. What the
float step's upper bound asks of its input set.

## Inputs
* `sys` – linear system
* `r` – float step length
* `η` – Taylor order
* `U` – input float zonotope

## Hypotheses
* `hr` – step length nonnegative
* `hη` – order admissible
* `hU` – input error box contains zero

## Conclusion
* the float input solution's error box contains zero
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
    (hr : 0 ≤ toReal r) {η : ℕ} (hη : sys.IsOrderAdmissibleFloat r r η) {U : Zonotope (Vec 𝕋 n)}
    (hU : (0 : Vec ℝ n) ∈ U.I_error.construct) : -- --- CONCL ---
    (0 : Vec ℝ n) ∈ (sys.inputSolutionFloat r η U).I_error.construct := by -- --- PROOF ---
  show (0 : Vec ℝ n) ∈ ((Zonotope.plus _ _).materialise).I_error.construct
  rw [Zonotope.materialise_eq]
  refine Zonotope.zero_mem_plus_error (sys.zero_mem_inputTaylorSumFloat_error hr hU η) ?_
  show (0 : Vec ℝ n) ∈ ((Zonotope.mtimesIntervalMat _ U).materialise).I_error.construct
  rw [Zonotope.materialise_eq]
  exact Zonotope.zero_mem_mtimesIntervalMat_error (sys.zero_mem_intervalInputRemainder hr hη) hU

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
