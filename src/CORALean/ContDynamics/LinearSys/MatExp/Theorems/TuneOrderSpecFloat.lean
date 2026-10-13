import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SideConditionOfLeFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.TuneOrderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Definitions.OrderAdmissible
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat

/-!
# The order `tuneOrder` returns is admissible

`orderTest` accepting `η` gives `nrm ≤ (η + 2)/2` and a float remainder bound strictly under
`ε`; `expRemainderBound_le` carries the bound through to the real remainder bound at any `x` of
norm at most `nrm`, so `OrderAdmissible` of [1]'s truncation order holds at `toReal ε`. The
search starts at `2`, so `2 ≤ η` is by construction. Minimality is not claimed.

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

/-- Whatever `tuneOrder` returns is admissible for `ε`. -/
theorem MatExp.tuneOrder_spec {x : Mat ℝ n n} {nrm ε : 𝕋} {fuel η : ℕ}
    (hx : ‖x‖ ≤ toReal nrm) (h : MatExp.tuneOrder nrm ε fuel = some η) :
    Real.MatExp.OrderAdmissible x (toReal ε) η := by -- --- PROOF ---
  have htest := List.find?_some h
  obtain ⟨k, -, hk⟩ := List.mem_map.mp (List.mem_of_find?_eq_some h)
  rw [MatExp.orderTest, Bool.and_eq_true] at htest
  obtain ⟨h1, h2⟩ := htest
  have hnn : 0 ≤ toReal nrm := le_trans (norm_nonneg _) hx
  have hε := MatExp.sideCondition_of_le h1
  have hpos : (0 : ℝ) < (η : ℝ) + 2 := by positivity
  refine ⟨by omega, ?_, ?_⟩
  · exact lt_of_le_of_lt (MatExp.expRemainderBound_le η hx hnn hε) (toReal_lt_of_ltStrict h2)
  · calc ‖x‖ / ((η : ℝ) + 2) ≤ toReal nrm / ((η : ℝ) + 2) := by gcongr
      _ < 1 := lt_of_le_of_lt hε (by norm_num)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
