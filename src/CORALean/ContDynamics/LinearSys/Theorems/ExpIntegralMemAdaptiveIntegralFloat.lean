module

public import CORALean.ContDynamics.LinearSys.Definitions.OrderAdmissibleFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveIntegralFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AdaptiveIntegralOuterRefines
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegralSubSumMemAdaptiveRemainder

@[expose] public section

/-!
# The integral of the exponential is in the float interval matrix

`∫₀^Δt e^{Aσ}dσ` is in the exact `adaptiveIntegral` (`expIntegral_sub_sum_mem_adaptiveRemainder`),
which the float one refines (`adaptiveIntegral_outer_refines`) at an order the float remainder
bound admits.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order

## Hypotheses
* `hΔt` – step length nonnegative
* `hη` – order admissible

## Conclusion
* the integral of the exponential lies in the float interval matrix
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.expIntegral_mem_adaptiveIntegralFloat (sys : LinearSys 𝕋 n) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 ≤ toReal Δt) (hη : sys.OrderAdmissibleFloat Δt Δt η) : -- --- CONCL ---
    Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal Δt)
      ∈ (MatExp.adaptiveIntegral (Interval.point sys.A) Δt η).construct := by -- --- PROOF ---
  -- the integrated exponential is in the exact `adaptiveIntegral`, so in the float one
  have hint : Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal Δt)
      ∈ (Real.MatExp.adaptiveIntegral (Scalar.toRealMat sys.A) (toReal Δt) η).construct := by
    refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
    have hmem := Real.Interval.mem_mat_iff.mp
      (Real.MatExp.expIntegral_sub_sum_mem_adaptiveRemainder (Scalar.toRealMat sys.A) hΔt η) j k
    simp only [Real.MatExp.adaptiveIntegral, Real.MatExp.adaptiveRemainder,
      Matrix.sub_apply] at hmem ⊢
    constructor <;> linarith [hmem.1, hmem.2]
  exact MatExp.adaptiveIntegral_outer_refines (Interval.point sys.A) hΔt η hη.2
    (Interval.mem_point sys.A) hint

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
