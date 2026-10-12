import CORALean.ContDynamics.LinParamSys.LinParamSys

/-!
# `LinParamSys.simulateEndTimeCora`, the last time stamp CORA's `linParamSys/simulate` returns

CORA's `@linParamSys/simulate.m` runs `ode45` once per input column (`k = size(params.u,2)`, l. 90)
on `tSpan`. Without `timeStep` that is `[params.tStart, params.tFinal]` (l. 76), the whole
horizon: `tFinal = params.tFinal/k` (l. 67) is only used with `timeStep`, and even there it drops
the `- params.tStart` that `@nonlinParamSys/simulate.m` (l. 65) has. Each segment's times are
shifted by the last time so far (`t = [t t_'+t(end)]`, l. 120), so the last time after `i`
segments is `i · tFinal`, not `tFinal`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The last time stamp in `t` after `i` input segments, `tSpan = [tStart, tFinal]`. -/
def LinParamSys.simulateEndTimeCora (tFinal : ℝ) : ℕ → ℝ
  | 0 => 0                                                        -- t = []
  | i + 1 => tFinal + simulateEndTimeCora tFinal i                -- t = [t t_'+t(end)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
