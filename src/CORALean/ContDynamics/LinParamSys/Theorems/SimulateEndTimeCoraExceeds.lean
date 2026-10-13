import CORALean.ContDynamics.LinParamSys.Operations.SimulateEndTimeCora

/-!
# CORA's `linParamSys/simulate` returns times beyond `tFinal`

With `tStart = 0`, `tFinal = 1`, no `timeStep` and an input `u` of two columns, the last time of
the trajectory `simulate` returns is `2 > tFinal` (`@linParamSys/simulate.m`, l. 67, 76, 120). A
wrong trajectory, not a reachable-set soundness issue.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.simulateEndTimeCora_exceeds :
    simulateEndTimeCora 1 2 = 2 ∧ (1 : ℝ) < simulateEndTimeCora 1 2 := by
  have h : simulateEndTimeCora 1 2 = 2 := by
    simp [simulateEndTimeCora]; norm_num
  exact ⟨h, by rw [h]; norm_num⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
