module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosureFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylorFloat
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter

@[expose] public section

/-!
# The float bound `W` holds the entrywise remainder `E(Δt,η)`

`E(Δt,η) = e^{|A|Δt} − Σ_{i≤η}(|A|Δt)ⁱ/i!`, with `|A|Δt` in the box `[|A|Δt]`: `e^{|A|Δt}` is in
`expIntervalEnclosure` of the box at the order `ηe` when `‖|A|Δt‖ ≤ (ηe + 2)/2`, the series is in
`expIntervalTaylor` at `η`, and the rounded-up difference of the enclosure's upper end and the
series' lower end is over `E(Δt,η)`.

## Inputs
* `A` – float system matrix
* `Δt` – float step length
* `η` – Taylor order of the step
* `ηe` – Taylor order of the admissible enclosure; the enclosure runs at `ηe + 8`
* `j` – row index
* `k` – column index

## Hypotheses
* `hε` – float norm bound of `[|A|Δt]` small enough for the order of the enclosure

## Conclusion
* the entry of the exact remainder is under the stored float bound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   12-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expRemainderMat_le_expRemainderEntrywise (A : Mat 𝕋 n n) {Δt : 𝕋}
    (η ηe : ℕ)
    (hε : toReal (MatExp.normUpperBound (Interval.smul Δt Δt
      (Interval.point (Interval.magnitudeMat (Interval.point A))))) / ((ηe : ℝ) + 2) ≤ 1 / 2)
    (j k : Fin n) : -- --- CONCL ---
    Real.MatExp.expRemainderMat (toRealMat A) (toReal Δt) η j k
      ≤ toReal (MatExp.expRemainderEntrywise A Δt η ηe j k) := by -- --- PROOF ---
  set B := Interval.smul Δt Δt (Interval.point (Interval.magnitudeMat (Interval.point A)))
    with hB
  -- `Δt |A|` is in the box
  have hAbs : Real.MatExp.absMat (toRealMat A) ∈
      (Interval.point (Interval.magnitudeMat (Interval.point A))).toSet := by
    have h := Interval.mem_point (Interval.magnitudeMat (Interval.point A))
    have e : RealImage.realImage (Interval.magnitudeMat (Interval.point A))
        = Real.MatExp.absMat (toRealMat A) := by
      funext i j
      simp only [RealImage.realImage, toRealMat, Interval.magnitudeMat, toReal_maximum,
        toReal_absolute, Real.MatExp.absMat, Interval.point, max_self]
    rwa [e] at h
  -- the scaled matrix is in the box
  have hmem : toReal Δt • Real.MatExp.absMat (toRealMat A) ∈ B.toSet :=
    Interval.smul_outer le_rfl le_rfl _ hAbs
  -- the norm condition at `ηe` is the same at `ηe + 8`
  have hε8 : toReal (MatExp.normUpperBound B) / (((ηe + 8 : ℕ) : ℝ) + 2) ≤ 1 / 2 := by
    rcases le_or_gt 0 (toReal (MatExp.normUpperBound B)) with h0 | h0
    · refine le_trans (div_le_div_of_nonneg_left h0 (by positivity) ?_) hε
      push_cast; linarith
    · have : toReal (MatExp.normUpperBound B) / (((ηe + 8 : ℕ) : ℝ) + 2) < 0 :=
        div_neg_of_neg_of_pos h0 (by positivity)
      linarith
  -- the enclosure at `ηe + 8` holds the exponential, the Taylor box the series
  have henc := Real.Interval.mem_mat_iff.mp
    (MatExp.exp_mem_expIntervalEnclosure B (ηe + 8) hmem hε8) j k
  have htay := Real.Interval.mem_mat_iff.mp (MatExp.expTaylor_mem_expIntervalTaylor B hmem η) j k
  simp only [Interval.nominal, RealImage.realImage, toRealMat] at henc htay
  have hsub := sub_le_subUp ((MatExp.expIntervalEnclosure B (ηe + 8)).sup j k)
    ((MatExp.expIntervalTaylor B η).inf j k)
  simp only [MatExp.expRemainderEntrywise, ← hB, Interval.materialiseMat_eq]
  simp only [Real.MatExp.expRemainderMat, Matrix.sub_apply]
  linarith [henc.2, htay.1]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
