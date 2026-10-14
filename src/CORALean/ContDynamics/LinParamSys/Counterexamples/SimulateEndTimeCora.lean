module

public import CORALean.ContDynamics.LinParamSys.LinParamSys

@[expose] public section

/-!
# `LinParamSys.simulateEndTimeCora`, the last time stamp CORA's `linParamSys/simulate` returns

CORA's `@linParamSys/simulate.m` runs `ode45` once per input column (`k = size(params.u,2)`, l. 90)
on `tSpan`. Without `timeStep` that is `[params.tStart, params.tFinal]` (l. 76), the whole
horizon: `tFinal = params.tFinal/k` (l. 67) is only used with `timeStep`, and even there it drops
the `- params.tStart` that `@nonlinParamSys/simulate.m` (l. 65) has. Each segment's times are
shifted by the last time so far (`t = [t t_'+t(end)]`, l. 120), so the last time after `i`
segments is `i · tFinal`, not `tFinal`.

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


-- The model: CORA's code as printed, kept only to be refuted.
/-- The last time stamp in `t` after `i` input segments, `tSpan = [tStart, tFinal]`. -/
def LinParamSys.simulateEndTimeCora (tFinal : ℝ) : ℕ → ℝ
  | 0 => 0                                                        -- t = []
  | i + 1 => tFinal + simulateEndTimeCora tFinal i                -- t = [t t_'+t(end)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.simulateEndTimeCora_exceeds :
    simulateEndTimeCora 1 2 = 2 ∧ (1 : ℝ) < simulateEndTimeCora 1 2 := by
  have h : simulateEndTimeCora 1 2 = 2 := by
    simp [simulateEndTimeCora]; norm_num
  exact ⟨h, by rw [h]; norm_num⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
