import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubOneLeExpNorm
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepError
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepErrorFloat
import CORALean.ContDynamics.LinearSys.Theorems.ExpNormTermsLeFloat
import CORALean.ContSet.Zonotope.Float.Theorems.SumAbsBoundLeSumUpAbsBoundError

/-!
# `timeIntervalStepErrorFloat` bounds `timeIntervalStepError`

`‖e^{rA} - I‖ ≤ e^x - 1` (`norm_exp_sub_one_le_exp_norm`) at `x = r‖A‖`, under its float
bound by `expNormTerms_le_float`; the curvature bracket as in
`timeIntervalStepCurvatureError_le_float`. Every factor is nonnegative, so the products keep
the order.
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
theorem LinearSys.timeIntervalStepError_le_float (sys : LinearSys 𝕋 n) {r : 𝕋} {η : ℕ}
    (hr : 0 ≤ toReal r) (hη : sys.OrderAdmissibleFloat r r η) (Z : Zonotope 𝕋 n) :
    sys.timeIntervalStepError (toReal r) η (nominal Z)
      ≤ toReal (sys.timeIntervalStepErrorFloat r η Z) := by -- --- PROOF ---
  obtain ⟨hx, hlin, hquad, hrem0, hrem⟩ := sys.expNormTerms_le_float hr hη
  have hS := Zonotope.sum_absBound_le_sumUp_absBoundError Z
  have hS0 : 0 ≤ ∑ j, Real.Zonotope.absBound (nominal Z) j :=
    Finset.sum_nonneg fun _ _ =>
      add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have h2S : 2 * ∑ j, Real.Zonotope.absBound (nominal Z) j
      ≤ toReal (addUp (sumUp fun j => Z.absBoundError j) (sumUp fun j => Z.absBoundError j)) :=
    le_trans (by linarith) (add_le_addUp _ _)
  set x := toReal r * ‖Scalar.toRealMat sys.A‖ with hxdef
  have hq0 : 0 ≤ Real.exp x - 1 - x := by linarith [Real.add_one_le_exp x]
  -- the hull term: `‖e^{rA} - I‖ ≤ e^{‖rA‖} - 1 = e^x - 1`, under its float bound
  have hnorm : ‖toReal r • Scalar.toRealMat sys.A‖ = x := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  have hhull : ‖NormedSpace.exp (toReal r • Scalar.toRealMat sys.A) - 1‖
      ≤ toReal (subUp (sys.expNormUpFloat r η) one) :=
    le_trans (Real.norm_exp_sub_one_le_exp_norm _) (by rw [hnorm]; exact hlin)
  have hbr := add_le_add hquad hrem
  refine le_trans ?_ (mul_le_mulUp _ _)
  refine mul_le_mul hS ?_ (add_nonneg (norm_nonneg _) (by positivity)) (hS0.trans hS)
  refine le_trans ?_ (add_le_addUp _ _)
  refine add_le_add hhull (le_trans ?_ (add_le_addUp _ _))
  have h1 := le_trans hbr (add_le_addUp _ _)
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
