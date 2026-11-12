module

public import CORALean.Global.Interfaces
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinearStep

@[expose] public section

/-!
# The options of CORA's adaptive `'lin'` algorithm

`LinReachAdaptiveOptions`: what CORA's `reach_adaptive` and `linReach_adaptive` read from
`params` and `options` at `alg = 'lin-adaptive'`, with the constants `postProcessing` sets
(`decrFactor = 0.9`, `zetaphi = [0.85; 0.76; 0.68]`, `zetaK = 0.9`) and the literals of the code
(`0.01`, `1.1`, `1e-3`, ...) as fields, so that a float run reads each as the double CORA uses.
The scalar `τ` is `𝕋` for a float run. `taylorTerms` is the truncation order of the linear step and
of `errorSolution_adaptive`, fixed where CORA tunes it by `zetaTlin`, `zetaTabs`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   11-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The `params` and `options` of CORA's `lin-adaptive`, its tuning constants and literals. -/
structure NonlinearSys.LinReachAdaptiveOptions (τ : Type) where
  /-- `params.tStart`. -/
  tStart : ℚ
  /-- `params.tFinal`. -/
  tFinal : ℚ
  /-- `taylorTerms` of the linear step and of the error solution. -/
  taylorTerms : ℕ
  /-- Girard order inside the linear step; CORA reduces adaptively instead, so an order above the
  sets' keeps CORA's sets. -/
  zonotopeOrder : ℕ
  /-- `options.redFactor`, `zeta_Z`. -/
  redFactor : τ
  /-- `options.decrFactor`, `0.9`. -/
  decrFactor : τ
  /-- `options.zetaphi`, indexed by `minorder`. -/
  zetaphi : Fin 3 → τ
  /-- `options.zetaK`, `0.9`. -/
  zetaK : τ
  /-- `0.01`, the first finite horizon relative to the time horizon. -/
  initFactor : τ
  /-- `1.1`, the enlargement of the admissible error and of a stalled horizon. -/
  enlarge : τ
  /-- `1e-3`, the tolerance of `withinTol(finitehorizon, stepsize, 1e-3)`. -/
  horizonTol : τ
  /-- `1e-8`, `withinTol`'s default, for a zero-width dimension. -/
  zeroTol : τ
  /-- `1e-9`, the residual tolerance of `aux_varphiest`'s bisection. -/
  varphiTol : τ
  /-- `1e-6`, the step tolerance of `aux_varphiest`'s bisection. -/
  varphiStep : τ
  /-- `1e-12`, the remaining time below which `reach_adaptive` stops. -/
  endTol : τ
  /-- `1e9`, `aux_checkForAbortion`'s ratio of remaining time to the last ten steps. -/
  abortRatio : τ
  /-- Precision of the square roots, exponentials and logarithms. -/
  prec : ℕ
  /-- Bound on every loop CORA writes as `while true`. -/
  fuel : ℕ
  /-- The linear step of every pass: `reachFloatInput`, or CORA's `oneStep` in closed form. -/
  linearStep : NonlinearSys.LinearStep := .reachFloatInput

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
