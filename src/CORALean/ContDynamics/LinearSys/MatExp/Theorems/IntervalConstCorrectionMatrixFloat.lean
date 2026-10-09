import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrixFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalConstCorrTermFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat

/-!
# The integrated interpolation error of every member lies in the float `F̃`

Through the exact point correction: `Real.MatExp.expIntegralDiff_mem_constCorrectionMatrix` at
the member `M` bounds each entry by sums of `min/max (constCorrTerm, 0)` widened by
`r · E(r M)`; `constCorrTerm_mem_intervalConstCorrTerm` puts each order inside the float term,
`sumDown_le_sum`/`sum_le_sumUp` carry the orders through the rounded sums, and
`expRemainderBound_le` the remainder. `hε` asks `1/2`, as the float remainder bound does,
where the exact one asks `< 1`. This is the float `G` of `curvatureEnclosure`: the true object
`∫₀ᵗ e^{Mσ}dσ - (t/r)∫₀ʳ e^{Mσ}dσ` of every matrix the box holds is in it.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- two rounded sums over `Fin η` compared with the exact `Finset.range` sums, entrywise
set_option maxHeartbeats 400000 in
theorem MatExp.expIntegralDiff_mem_intervalConstCorrectionMatrix (A : Interval (Mat 𝕋 n n))
    {r : 𝕋} (hr : 0 < toReal r) (η : ℕ)
    (hε : toReal (MatExp.normUpperBound (Interval.smul r r A)) / ((η : ℝ) + 2) ≤ 1 / 2)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ toReal r) :
    Real.MatExp.expIntegral M t - (t / toReal r) • Real.MatExp.expIntegral M (toReal r)
      ∈ (MatExp.intervalConstCorrectionMatrix A r η).construct := by -- --- PROOF ---
  have hnorm := MatExp.norm_smul_le_normUpperBound A r hM
  have hden : (0 : ℝ) < (η : ℝ) + 2 := by positivity
  have hε' : ‖toReal r • M‖ / ((η : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (le_trans (div_le_div_of_nonneg_right hnorm hden.le) hε) (by norm_num)
  have hE := MatExp.expRemainderBound_le η hnorm (le_trans (norm_nonneg _) hnorm) hε
  -- the exact point statement, at the member
  have hX := Real.Interval.mem_mat_iff.mp
    (Real.MatExp.expIntegralDiff_mem_constCorrectionMatrix M hr η hε' ht0 htr)
  refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
  obtain ⟨h1, h2⟩ := hX j k
  simp only [Real.MatExp.constCorrectionMatrix] at h1 h2
  have hterm := fun i : ℕ => MatExp.constCorrTerm_mem_intervalConstCorrTerm A hr.le i hM j k
  -- the stored orders, rounded and summed, bracket the exact sums
  have hlo : toReal (sumDown fun i : Fin η =>
        minimum ((MatExp.intervalConstCorrTerm A r i).inf j k) zero)
      ≤ ∑ i ∈ Finset.range η, min (Real.MatExp.constCorrTerm M (toReal r) i j k) 0 := by
    refine le_trans (sumDown_le_sum _) ?_
    rw [← Fin.sum_univ_eq_sum_range (fun i => min (Real.MatExp.constCorrTerm M _ i j k) 0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [toReal_minimum, toReal_zero]
    exact min_le_min_right _ (hterm i).1
  -- and the same from above
  have hhi : ∑ i ∈ Finset.range η, max (Real.MatExp.constCorrTerm M (toReal r) i j k) 0
      ≤ toReal (sumUp fun i : Fin η =>
        maximum ((MatExp.intervalConstCorrTerm A r i).sup j k) zero) := by
    refine le_trans ?_ (sum_le_sumUp _)
    rw [← Fin.sum_univ_eq_sum_range (fun i => max (Real.MatExp.constCorrTerm M _ i j k) 0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [toReal_maximum, toReal_zero]
    exact max_le_max_right _ (hterm i).2
  -- the tail `r E(r)` and the rounded sums bracket the exact entry
  set E := MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul r r A)) η
  have hrE : toReal r * Real.MatExp.expRemainderBound (toReal r • M) η ≤ toReal (mulUp r E) :=
    le_trans (mul_le_mul_of_nonneg_left hE hr.le) (mul_le_mulUp _ _)
  set sLo := sumDown fun i : Fin η =>
    minimum ((MatExp.intervalConstCorrTerm A r i).inf j k) zero
  set sHi := sumUp fun i : Fin η =>
    maximum ((MatExp.intervalConstCorrTerm A r i).sup j k) zero
  simp only [MatExp.intervalConstCorrectionMatrix, Interval.materialiseMat_eq, Interval.nominal,
    RealImage.realImage, toRealMat, Fin.getElem_fin, Vector.getElem_ofFn]
  show toReal (subDown sLo (mulUp r E)) ≤ _ ∧ _ ≤ toReal (addUp sHi (mulUp r E))
  have hsd := subDown_le_sub sLo (mulUp r E)
  have hau := add_le_addUp sHi (mulUp r E)
  exact ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
