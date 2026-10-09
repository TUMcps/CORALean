import CORALean.ContDynamics.LinearSys.Operations.TimePointStepError
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepErrorFloat
import CORALean.ContDynamics.LinearSys.Theorems.ExpNormTermsLeFloat
import CORALean.ContSet.Zonotope.Float.Theorems.SumAbsBoundLeSumUpAbsBoundError

/-!
# `timePointStepErrorFloat` bounds `timePointStepError`

Every factor of `2 Σⱼ|U|ⱼ r ((e^x - 1) + E(rA, η))` under its float bound, `r` itself
exact; all are nonnegative, so the products keep the order.
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

/-- At `r ≥ 0` and an admissible `η`, the float estimate is at least the real one at `U`'s
nominal zonotope. -/
theorem LinearSys.timePointStepError_le_float (sys : LinearSys 𝕋 n) {r : 𝕋} {η : ℕ}
    (hr : 0 ≤ toReal r) (hη : sys.OrderAdmissibleFloat r r η) (Z : Zonotope 𝕋 n) :
    sys.timePointStepError (toReal r) η (nominal Z)
      ≤ toReal (sys.timePointStepErrorFloat r η Z) := by -- --- PROOF ---
  obtain ⟨hx, hlin, hquad, hrem0, hrem⟩ := sys.expNormTerms_le_float hr hη
  have hS := Zonotope.sum_absBound_le_sumUp_absBoundError Z
  have hS0 : 0 ≤ ∑ j, Real.Zonotope.absBound (nominal Z) j :=
    Finset.sum_nonneg fun _ _ =>
      add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have h2S : 2 * ∑ j, Real.Zonotope.absBound (nominal Z) j
      ≤ toReal (addUp (sumUp fun j => Z.absBoundError j) (sumUp fun j => Z.absBoundError j)) :=
    le_trans (by linarith) (add_le_addUp _ _)
  have hl0 : 0 ≤ Real.exp (toReal r * ‖Scalar.toRealMat sys.A‖) - 1 := by
    linarith [Real.add_one_le_exp (toReal r * ‖Scalar.toRealMat sys.A‖),
      mul_nonneg hr (norm_nonneg (Scalar.toRealMat sys.A))]
  -- `(2 S) r` times the bracket, each under its float bound
  refine le_trans ?_ (mul_le_mulUp _ _)
  refine mul_le_mul ?_ (le_trans (add_le_add hlin hrem) (add_le_addUp _ _))
    (add_nonneg hl0 hrem0) ?_
  · exact le_trans (mul_le_mul_of_nonneg_right h2S hr) (mul_le_mulUp _ _)
  · exact le_trans (mul_nonneg (le_trans (by linarith) h2S) hr) (mul_le_mulUp _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
