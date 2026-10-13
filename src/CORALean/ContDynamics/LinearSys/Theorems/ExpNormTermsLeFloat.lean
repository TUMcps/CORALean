import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
import CORALean.ContDynamics.LinearSys.Theorems.ExpLeExpNormUpFloat
import CORALean.ContSet.Interval.Float.Theorems.MemPoint

/-!
# The scalar terms of a step's error estimates, bounded in floats

What `timeIntervalStepError` and its relatives are built from, at `x = r‖A‖`: `x` itself,
`e^x - 1`, `e^x - 1 - x` and the remainder bound `E(rA, η)`, each under its float
counterpart at `nrm ≥ x`. The second and third are monotone in `x ≥ 0`, so `expNormUpFloat`,
which bounds `e^{nrm}`, bounds them at `nrm`; the remainder is `expRemainderBound_le`, and is
nonnegative because the admissible `η` keeps its geometric factor positive.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- At `r ≥ 0` and an admissible `η`: `r‖A‖ ≤ nrm`, `e^{r‖A‖} - 1` and `e^{r‖A‖} - 1 - r‖A‖`
under their float bounds, and `0 ≤ E(rA, η) ≤` its float bound. -/
theorem LinearSys.expNormTerms_le_float (sys : LinearSys 𝕋 n) {r : 𝕋} {η : ℕ}
    (hr : 0 ≤ toReal r) (hη : sys.OrderAdmissibleFloat r r η) :
    toReal r * ‖Scalar.toRealMat sys.A‖
        ≤ toReal (MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A))) ∧
      Real.exp (toReal r * ‖Scalar.toRealMat sys.A‖) - 1
        ≤ toReal (subUp (sys.expNormUpFloat r η) one) ∧
      Real.exp (toReal r * ‖Scalar.toRealMat sys.A‖) - 1 - toReal r * ‖Scalar.toRealMat sys.A‖
        ≤ toReal (subUp (subUp (sys.expNormUpFloat r η) one)
          (MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A)))) ∧
      0 ≤ Real.MatExp.expRemainderBound (toReal r • Scalar.toRealMat sys.A) η ∧
      Real.MatExp.expRemainderBound (toReal r • Scalar.toRealMat sys.A) η
        ≤ toReal (MatExp.expRemainderBound
          (MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A)))
          η) := by -- --- PROOF ---
  set A := Scalar.toRealMat sys.A with hA
  set nrm := MatExp.normUpperBound (Interval.smul r r (Interval.point sys.A)) with hnrm
  set x := toReal r * ‖A‖ with hx
  set a := toReal nrm with ha
  have hnorm : ‖toReal r • A‖ = x := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  have hxa : x ≤ a := hnorm ▸ MatExp.norm_smul_le_normUpperBound _ r (Interval.mem_point sys.A)
  have hx0 : 0 ≤ x := mul_nonneg hr (norm_nonneg _)
  have hE := sys.exp_le_expNormUpFloat hη
  rw [← hnrm, ← ha] at hE
  -- `e^a - e^x ≥ a - x` for `0 ≤ x ≤ a`, which is what makes both terms monotone
  have hexa : Real.exp x ≤ Real.exp a := Real.exp_le_exp.mpr hxa
  have hgap : a - x ≤ Real.exp a - Real.exp x := by
    have h1 := Real.add_one_le_exp (a - x)
    have h2 : 1 ≤ Real.exp x := Real.one_le_exp hx0
    have h3 : Real.exp a = Real.exp x * Real.exp (a - x) := by rw [← Real.exp_add]; ring_nf
    nlinarith
  have hhull : Real.exp x - 1 ≤ toReal (subUp (sys.expNormUpFloat r η) one) := by
    refine le_trans ?_ (sub_le_subUp _ _)
    rw [toReal_one]; linarith
  -- the remainder's geometric factor is at least `1/2`, at `‖rA‖ ≤ nrm`
  have h2 : (0 : ℝ) < (η : ℝ) + 2 := by positivity
  have hq : x / ((η : ℝ) + 2) ≤ 1 / 2 :=
    le_trans (div_le_div_of_nonneg_right hxa h2.le) hη.2
  refine ⟨hxa, hhull, ?_, ?_, ?_⟩
  · refine le_trans ?_ (sub_le_subUp _ _)
    refine le_trans ?_ (sub_le_sub_right (le_trans (by rw [toReal_one]) (sub_le_subUp _ _)) _)
    linarith
  · rw [Real.MatExp.expRemainderBound, hnorm]
    refine mul_nonneg (div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _)) ?_
    exact inv_nonneg.mpr (by linarith)
  · exact MatExp.expRemainderBound_le η (hnorm.le.trans hxa) (hx0.trans hxa)
      (le_trans (div_le_div_of_nonneg_right le_rfl h2.le) hη.2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
