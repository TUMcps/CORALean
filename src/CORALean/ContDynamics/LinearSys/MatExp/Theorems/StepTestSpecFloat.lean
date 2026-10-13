module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SideConditionOfLeFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.StepTestFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.StepAdmissible
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat

@[expose] public section

/-!
# A step passing `stepTest` is admissible

`stepTest` accepting `r` gives `0 < r`; the float norm bound `q = r · nrm` is above
`‖r • A‖ = r ‖A‖` (`mul_le_mulUp`) and meets the side condition; and the float contribution
`r · expRemainderBound q η` is strictly under `ε`, which `expRemainderBound_le` at `q` and
`mul_le_mulUp` bring down to the contribution of `StepAdmissible`, [1]'s step predicate.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A candidate passing `stepTest` is admissible. -/
theorem MatExp.stepTest_spec {A : Mat ℝ n n} {nrm ε r : 𝕋} {η : ℕ}
    (hA : ‖A‖ ≤ toReal nrm) (h : MatExp.stepTest nrm ε η r = true) :
    Real.MatExp.StepAdmissible A η (toReal ε) (toReal r) := by -- --- PROOF ---
  rw [MatExp.stepTest, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hr : 0 < toReal r := by
    have := toReal_lt_of_ltStrict h0
    rwa [toReal_zero] at this
  have hnorm : ‖toReal r • A‖ ≤ toReal (mulUp r nrm) := by
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    exact le_trans (mul_le_mul_of_nonneg_left hA hr.le) (mul_le_mulUp r nrm)
  have hnn : 0 ≤ toReal (mulUp r nrm) := le_trans (norm_nonneg _) hnorm
  have hε := MatExp.sideCondition_of_le h1
  -- the contribution, then the side condition
  refine ⟨hr, ?_, ?_⟩
  · have hb := MatExp.expRemainderBound_le (𝕋 := 𝕋) η hnorm hnn hε
    calc toReal r * Real.MatExp.expRemainderBound (toReal r • A) η
        ≤ toReal r * toReal (MatExp.expRemainderBound (mulUp r nrm) η) :=
          mul_le_mul_of_nonneg_left hb hr.le
      _ ≤ toReal (mulUp r (MatExp.expRemainderBound (mulUp r nrm) η)) := mul_le_mulUp _ _
      _ < toReal ε := toReal_lt_of_ltStrict h2
  · have hpos : (0 : ℝ) < (η : ℝ) + 2 := by positivity
    calc ‖toReal r • A‖ / ((η : ℝ) + 2) ≤ toReal (mulUp r nrm) / ((η : ℝ) + 2) := by gcongr
      _ < 1 := lt_of_le_of_lt hε (by norm_num)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
