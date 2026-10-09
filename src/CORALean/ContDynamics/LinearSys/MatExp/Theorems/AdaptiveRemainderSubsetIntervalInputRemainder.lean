import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat
import CORALean.ContSet.Interval.Float.Theorems.MemMatIff
import CORALean.ContSet.Interval.Real.Theorems.MemMat

/-!
# `errorSolution_adaptive`'s remainder box, inside the float input remainder

`adaptiveRemainder` is `Δt [-W, W]` with `W = |E(Δt, η)|` entrywise, `E` the Taylor tail of
`e^{Δt|A|}`. An entry of `E` is at most its `l∞` norm, which the tail bound takes at
`‖Δt|A|‖ = ‖Δt A‖` (the row sums of `|A|` are those of `A`), and that is under the float
remainder bound `intervalInputRemainder` is built from. So the float box, `Δt` times one bound
in every entry, holds the exact one at every member of the interval matrix.
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `|A|` has `A`'s row sums, so its `l∞` operator norm. -/
theorem aux_norm_absMat (M : Mat ℝ n n) : ‖Real.MatExp.absMat M‖ = ‖M‖ := by
  simp [Matrix.linfty_opNorm_def, Real.MatExp.absMat]


-- =======================================  MAIN THEOREM  ======================================= --

/-- At every member `M` of `A` and an order the float remainder admits, the exact
`Δt [-|E|, |E|]` lies inside the float `[-E(Δt)·Δt, E(Δt)·Δt]`. -/
theorem MatExp.adaptiveRemainder_subset_intervalInputRemainder (A : Interval (Mat 𝕋 n n))
    {r : 𝕋} (hr : 0 ≤ toReal r) (η : ℕ)
    (hε : toReal (MatExp.normUpperBound (Interval.smul r r A)) / ((η : ℝ) + 2) ≤ 1 / 2)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) :
    (Real.MatExp.adaptiveRemainder M (toReal r) η).construct
      ⊆ (MatExp.intervalInputRemainder A r η).construct := by -- --- PROOF ---
  set nrm := MatExp.normUpperBound (Interval.smul r r A) with hnrm
  set Eb := MatExp.expRemainderBound nrm η with hEb
  -- `‖r|M|‖ = ‖rM‖ ≤ nrm`, so the tail bound applies at `r|M|`
  have hnorm : ‖toReal r • Real.MatExp.absMat M‖ ≤ toReal nrm := by
    rw [norm_smul, aux_norm_absMat, ← norm_smul]
    exact MatExp.norm_smul_le_normUpperBound A r hM
  have hnn : 0 ≤ toReal nrm := (norm_nonneg _).trans hnorm
  have h2 : (0 : ℝ) < (η : ℝ) + 2 := by positivity
  have hlt : ‖toReal r • Real.MatExp.absMat M‖ / ((η : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (le_trans (div_le_div_of_nonneg_right hnorm h2.le) hε) (by norm_num)
  -- every entry of `E` is under the float bound, and so is `r` times it
  have hentry : ∀ j k, toReal r * |Real.MatExp.expRemainderMat M (toReal r) η j k|
      ≤ toReal (mulUp r Eb) := fun j k => by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hr) (mul_le_mulUp _ _)
    calc |Real.MatExp.expRemainderMat M (toReal r) η j k|
        ≤ ‖Real.MatExp.expRemainderMat M (toReal r) η‖ := Real.abs_entry_le_norm _ j k
      _ ≤ Real.MatExp.expRemainderBound (toReal r • Real.MatExp.absMat M) η :=
          Real.norm_exp_sub_expTaylor_le _ η hlt
      _ ≤ toReal Eb := MatExp.expRemainderBound_le η hnorm hnn hε
  intro X hX
  have hX' := Real.Interval.mem_mat_iff.mp hX
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  simp only [Real.MatExp.adaptiveRemainder] at hX'
  simp only [MatExp.intervalInputRemainder, toReal_neg]
  have := hentry j k
  constructor <;> linarith [(hX' j k).1, (hX' j k).2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
