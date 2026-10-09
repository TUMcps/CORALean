import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepCurvatureError
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepCurvatureErrorFloat
import CORALean.ContDynamics.LinearSys.Theorems.ExpNormTermsLeFloat
import CORALean.ContSet.Zonotope.Float.Theorems.SumAbsBoundLeSumUpAbsBoundError

/-!
# `timeIntervalStepCurvatureErrorFloat` bounds `timeIntervalStepCurvatureError`

Every factor of `2 Σⱼ|X₀|ⱼ (e^x - 1 - x + E(rA, η))` under its float bound
(`expNormTerms_le_float`, `sum_absBound_le_sumUp_absBoundError`), all of them nonnegative, so
the products keep the order; the real side is read at the nominal zonotope, whose
`absBound` the float coordinate reaches cover.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic InflatedContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- At `r ≥ 0` and an admissible `η`, the float estimate is at least the real one at `X₀`'s
nominal zonotope. -/
theorem LinearSys.timeIntervalStepCurvatureError_le_float (sys : LinearSys 𝕋 n) {r : 𝕋} {η : ℕ}
    (hr : 0 ≤ toReal r) (hη : sys.OrderAdmissibleFloat r r η) (Z : Zonotope 𝕋 n) :
    sys.timeIntervalStepCurvatureError (toReal r) η (nominal Z)
      ≤ toReal (sys.timeIntervalStepCurvatureErrorFloat r η Z) := by -- --- PROOF ---
  obtain ⟨hx, hlin, hquad, hrem0, hrem⟩ := sys.expNormTerms_le_float hr hη
  have hS := Zonotope.sum_absBound_le_sumUp_absBoundError Z
  have hS0 : 0 ≤ ∑ j, Real.Zonotope.absBound (nominal Z) j :=
    Finset.sum_nonneg fun _ _ =>
      add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have h2S : 2 * ∑ j, Real.Zonotope.absBound (nominal Z) j
      ≤ toReal (addUp (sumUp fun j => Z.absBoundError j) (sumUp fun j => Z.absBoundError j)) :=
    le_trans (by linarith) (add_le_addUp _ _)
  have hq0 : 0 ≤ Real.exp (toReal r * ‖Scalar.toRealMat sys.A‖) - 1
      - toReal r * ‖Scalar.toRealMat sys.A‖ := by
    linarith [Real.add_one_le_exp (toReal r * ‖Scalar.toRealMat sys.A‖)]
  -- `2 S` times the bracket, each under its float bound
  refine le_trans ?_ (mul_le_mulUp _ _)
  refine mul_le_mul h2S (le_trans (add_le_add hquad hrem) (add_le_addUp _ _))
    (add_nonneg hq0 hrem0) (le_trans (by linarith) h2S)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
