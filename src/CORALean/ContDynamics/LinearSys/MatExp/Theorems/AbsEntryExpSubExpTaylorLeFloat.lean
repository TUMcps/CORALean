module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormUpperBoundFloat
public import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax

@[expose] public section

/-!
# An entry of the exponential's Taylor error, under a float norm bound

Entry by entry as `Real.MatExp.exp_mem_expIntervalEnclosure` does: `norm_le_absMax` and
`norm_absMax_le_normUpperBound` replace the pointwise tail bound by a uniform one at
`normUpperBound A`, and `expRemainderBound_le` rounds that bound to a float.

`hε` asks `1/2`, not `< 1`: `expRemainderBound_le`'s geometric factor is the fixed constant `2`,
sound only under the stronger margin.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The pointwise tail bound, taken uniformly at `normUpperBound A` and already
rounded to a float. -/
theorem MatExp.abs_entry_exp_sub_expTaylor_le (A : Interval (Mat 𝕋 n n)) (η : ℕ) {M : Mat ℝ n n}
    (hM : M ∈ A.construct) (hε : toReal (MatExp.normUpperBound A) / ((η : ℝ) + 2) ≤ 1 / 2)
    (i j : Fin n) : -- --- CONCL ---
    |exp M i j - Real.MatExp.expTaylor M η i j|
      ≤ toReal (MatExp.expRemainderBound (MatExp.normUpperBound A) η) := by -- --- PROOF ---
  have hnorm : ‖M‖ ≤ toReal (MatExp.normUpperBound A) :=
    le_trans (Real.Interval.norm_le_absMax hM) (MatExp.norm_absMax_le_normUpperBound A)
  have hnn : (0 : ℝ) ≤ toReal (MatExp.normUpperBound A) := le_trans (norm_nonneg M) hnorm
  have h2 : (0 : ℝ) < (η : ℝ) + 2 := by positivity
  have hfrac : ‖M‖ / ((η : ℝ) + 2) ≤ toReal (MatExp.normUpperBound A) / ((η : ℝ) + 2) := by gcongr
  have hεM : ‖M‖ / ((η : ℝ) + 2) < 1 := lt_of_le_of_lt (le_trans hfrac hε) (by norm_num)
  calc |exp M i j - Real.MatExp.expTaylor M η i j|
      = |(exp M - Real.MatExp.expTaylor M η) i j| := by rw [Matrix.sub_apply]
    _ ≤ ‖exp M - Real.MatExp.expTaylor M η‖ := Real.abs_entry_le_norm _ i j
    _ ≤ Real.MatExp.expRemainderBound M η := Real.norm_exp_sub_expTaylor_le M η hεM
    _ ≤ toReal (MatExp.expRemainderBound (MatExp.normUpperBound A) η) :=
        MatExp.expRemainderBound_le η hnorm hnn hε

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
