import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrTermFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat

/-!
# The interpolation error of every member lies in the float correction

Through the exact point correction: `Real.MatExp.expDiff_mem_correctionMatrix`
at the member `M` bounds each entry by sums of `min/max (corrTerm, 0)` widened
by `E(r M)`; `corrTerm_mem_intervalCorrTerm` puts each order inside the float
term, `sumDown_le_sum`/`sum_le_sumUp` carry the orders through the rounded sums,
and `expRemainderBound_le` the remainder. `hε` asks `1/2`, as the float
remainder bound does, where the exact one asks `< 1`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expDiff_mem_intervalCorrectionMatrix (A : Interval (Mat 𝕋 n n)) {r : 𝕋}
    (hr : 0 < toReal r) {m : ℕ}
    (hε : toReal (MatExp.normUpperBound (Interval.smul r r A)) / (((m + 2 : ℕ) : ℝ) + 2)
      ≤ 1 / 2)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ toReal r) :
    exp (t • M) - 1 - (t / toReal r) • (exp (toReal r • M) - 1)
      ∈ (MatExp.intervalCorrectionMatrix A r (m + 2)).construct := by -- --- PROOF ---
  have hnorm := MatExp.norm_smul_le_normUpperBound A r hM
  have hden : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) + 2 := by positivity
  have hε' : ‖toReal r • M‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (le_trans (div_le_div_of_nonneg_right hnorm hden.le) hε) (by norm_num)
  have hE := MatExp.expRemainderBound_le (m + 2) hnorm (le_trans (norm_nonneg _) hnorm) hε
  have hX := Real.Interval.mem_mat_iff.mp
    (Real.MatExp.expDiff_mem_correctionMatrix M hr hε' ht0 htr)
  refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
  obtain ⟨h1, h2⟩ := hX j k
  simp only [Real.MatExp.correctionMatrix, show m + 2 - 1 = m + 1 from rfl] at h1 h2
  have hterm := fun i : ℕ =>
    MatExp.corrTerm_mem_intervalCorrTerm A hr.le (i := i + 2) (by omega) hM j k
  -- the stored orders, rounded and summed, bracket the exact sums
  have hlo : toReal (sumDown fun i : Fin (m + 1) =>
        minimum ((MatExp.intervalCorrTerm A r (i + 2)).inf j k) zero)
      ≤ ∑ i ∈ Finset.range (m + 1), min (Real.MatExp.corrTerm M (toReal r) (i + 2) j k) 0 := by
    refine le_trans (sumDown_le_sum _) ?_
    rw [← Fin.sum_univ_eq_sum_range (fun i => min (Real.MatExp.corrTerm M _ (i + 2) j k) 0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [toReal_minimum, toReal_zero]
    exact min_le_min_right _ (hterm i).1
  have hhi : ∑ i ∈ Finset.range (m + 1), max (Real.MatExp.corrTerm M (toReal r) (i + 2) j k) 0
      ≤ toReal (sumUp fun i : Fin (m + 1) =>
        maximum ((MatExp.intervalCorrTerm A r (i + 2)).sup j k) zero) := by
    refine le_trans ?_ (sum_le_sumUp _)
    rw [← Fin.sum_univ_eq_sum_range (fun i => max (Real.MatExp.corrTerm M _ (i + 2) j k) 0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [toReal_maximum, toReal_zero]
    exact max_le_max_right _ (hterm i).2
  -- the stored entry is the rounded difference and sum of exactly these
  set E := MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul r r A)) (m + 2)
  set sLo := sumDown fun i : Fin (m + 1) =>
    minimum ((MatExp.intervalCorrTerm A r (i + 2)).inf j k) zero
  set sHi := sumUp fun i : Fin (m + 1) =>
    maximum ((MatExp.intervalCorrTerm A r (i + 2)).sup j k) zero
  simp only [MatExp.intervalCorrectionMatrix, Interval.materialiseMat_eq, Interval.nominal,
    RealImage.realImage, toRealMat, Fin.getElem_fin, Vector.getElem_ofFn]
  show toReal (subDown sLo E) ≤ _ ∧ _ ≤ toReal (addUp sHi E)
  have hsd := subDown_le_sub sLo E
  have hau := add_le_addUp sHi E
  exact ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
