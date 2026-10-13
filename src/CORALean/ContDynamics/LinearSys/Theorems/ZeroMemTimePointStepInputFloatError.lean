module

public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepInputFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ZeroMemInputSolutionFloatError

@[expose] public section

/-!
# The float step keeps the origin in its error box

`[e^{Ar}] X` does, `[e^{Ar}]` holding the true exponential
(`exp_mem_expIntervalFloat`), so does the input solution, and so does their
float sum. What the next step of a float run asks of its operand before its
upper bounds apply.
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

/-- The float step keeps `0` in its error box, given `X` and `U` do. -/
theorem LinearSys.zero_mem_timePointStepInputFloat_error (sys : LinearSys 𝕋 n) {r : 𝕋}
    (hr : 0 ≤ toReal r) {η : ℕ} (hη : sys.OrderAdmissibleFloat r r η) {X U : Zonotope (Vec 𝕋 n)}
    (hX : (0 : Vec ℝ n) ∈ X.E.construct) (hU : (0 : Vec ℝ n) ∈ U.E.construct) :
    (0 : Vec ℝ n) ∈ (sys.timePointStepInputFloat r η X U).E.construct := by -- --- PROOF ---
  have he := sys.exp_mem_expIntervalFloat hη (t := toReal r) le_rfl le_rfl
  show (0 : Vec ℝ n) ∈ ((Zonotope.plus _ _).materialise).E.construct
  rw [Zonotope.materialise_eq]
  refine Zonotope.zero_mem_plus_error ?_ (sys.zero_mem_inputSolutionFloat_error hr hη hU)
  show (0 : Vec ℝ n) ∈ ((Zonotope.mtimesIntervalMat _ X).materialise).E.construct
  rw [Zonotope.materialise_eq]
  exact Zonotope.zero_mem_mtimesIntervalMat_error he hX

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
