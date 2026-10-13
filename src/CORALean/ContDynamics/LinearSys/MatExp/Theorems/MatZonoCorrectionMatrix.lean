import CORALean.ContDynamics.LinearSys.MatExp.Operations.MatZonoCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
import CORALean.ContSet.Interval.Real.Theorems.MemMat
import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
import CORALean.ContSet.Interval.Real.Theorems.SmulOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MatPowOuter

/-!
# The matrix-zonotope correction matrix contains every member's interpolation error

`expDiff_mem_intervalCorrectionMatrix` at a matrix zonotope: at every member `A`
of `M` and every `t ∈ [0, r]`, `e^{tA} - 1 - (t/r)(e^{rA} - 1)` lies in
`matZonoCorrectionMatrix M r η`. The point statement at `A` is widened term by
term: `A^i` lies in the `i`-th matrix-zonotope power (`Zonotope.matPow_outer`),
hence in its box, so each order's term at `A` is inside the boxed term; and the
member lies in `M`'s box, so its tail bound is under the box's.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `F` at a matrix zonotope contains the interpolation error of every
member, at every time of the step. -/
theorem MatExp.expDiff_mem_matZonoCorrectionMatrix (M : Zonotope (Mat ℝ n n)) {r : ℝ}
    (hr : 0 < r) {m : ℕ}
    (hε : ‖(Interval.smul r M.interval).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {A : Mat ℝ n n} (hA : A ∈ M.construct) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)
      ∈ (MatExp.matZonoCorrectionMatrix M r (m + 2)).construct := by -- --- PROOF ---
  have hAI : A ∈ M.interval.construct := Zonotope.interval_contains M hA
  have hnorm : ‖r • A‖ ≤ ‖(Interval.smul r M.interval).absMax‖ :=
    Interval.norm_le_absMax (Interval.smul_outer r M.interval hAI)
  have hεM : ‖r • A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (by gcongr) hε
  -- the point statement, at the member, is what everything below only widens
  have hpoint := MatExp.expDiff_mem_correctionMatrix A hr hεM ht0 htr
  have htail : MatExp.expRemainderBound (r • A) (m + 2)
      ≤ MatExp.expRemainderBound (Interval.smul r M.interval).absMax (m + 2) :=
    MatExp.expRemainderBound_mono (m + 2) hnorm hε
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  have hpk := Interval.mem_mat_iff.mp hpoint j k
  -- each kept order of the member sits inside the box of the zonotope power
  have hterm : ∀ i ∈ Finset.range (m + 2 - 1),
      (MatExp.matZonoCorrTerm M r (i + 2)).inf j k ≤ MatExp.corrTerm A r (i + 2) j k
        ∧ MatExp.corrTerm A r (i + 2) j k
            ≤ (MatExp.matZonoCorrTerm M r (i + 2)).sup j k := by
    intro i _
    have hs := Interval.smul_outer
      (MatExp.corrCoeff (i + 2) * r ^ (i + 2) * ((Nat.factorial (i + 2) : ℝ))⁻¹)
      (M.matPow (i + 2)).interval
      (Zonotope.interval_contains _ (Zonotope.matPow_outer M hA (i + 2)))
    have h := Interval.mem_mat_iff.mp hs j k
    have hval : ((MatExp.corrCoeff (i + 2) * r ^ (i + 2)
        * ((Nat.factorial (i + 2) : ℝ))⁻¹) • A ^ (i + 2)) j k
          = MatExp.corrTerm A r (i + 2) j k := by
      simp only [Matrix.smul_apply, smul_eq_mul, MatExp.corrTerm]
      ring
    rw [hval] at h
    exact h
  -- `min` and `max` are monotone, so the comparison survives the sum
  have hlow : ∑ i ∈ Finset.range (m + 2 - 1),
        min ((MatExp.matZonoCorrTerm M r (i + 2)).inf j k) 0
      ≤ ∑ i ∈ Finset.range (m + 2 - 1), min (MatExp.corrTerm A r (i + 2) j k) 0 :=
    Finset.sum_le_sum fun i hi => min_le_min (hterm i hi).1 (le_refl 0)
  have hupp : ∑ i ∈ Finset.range (m + 2 - 1), max (MatExp.corrTerm A r (i + 2) j k) 0
      ≤ ∑ i ∈ Finset.range (m + 2 - 1),
          max ((MatExp.matZonoCorrTerm M r (i + 2)).sup j k) 0 :=
    Finset.sum_le_sum fun i hi => max_le_max (hterm i hi).2 (le_refl 0)
  simp only [MatExp.correctionMatrix] at hpk
  simp only [MatExp.matZonoCorrectionMatrix]
  exact ⟨by linarith [hpk.1], by linarith [hpk.2]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
