module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# One step of an adaptive float run, as reported

`AdaptiveStepInfo`: what [1, Alg. 1] returns for step `i`, the window
`[t_i, t_{i+1}]` in absolute time and clipped to `t_f`, `R([t_i,t_{i+1}])`,
and the parameters and errors the tuning chose it at, CORA's `timeInt.time`,
`timeInt.set` and `tVec` together.

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- Step `i` of [1, Alg. 1]: its window, its set, and what it was tuned to. -/
structure LinearSys.AdaptiveStepInfo (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) where
  /-- `t_i`, absolute. -/
  tStart : ℚ
  /-- `t_{i+1}`, absolute and clipped to `tFinal`. -/
  tEnd : ℚ
  /-- `Δt_i`, which may overshoot `tFinal` at the last step. -/
  Δt : 𝕋
  /-- `Φ_prop,i`, the truncation order the step ran at. -/
  η : ℕ
  /-- `Φ_set,i`, the order `PR([0,t_{i+1}])` was reduced to. -/
  ρ : ℕ
  /-- `R([t_i,t_{i+1}])`. -/
  R : Zonotope (Vec 𝕋 n)
  /-- `ε_H([t_i,t_{i+1}])`, eq. (21). -/
  εH : ℚ
  /-- `ε_P([0,t_{i+1}])`, eq. (9). -/
  εP : ℚ
  /-- `ε_S([0,t_{i+1}])`, eq. (12). -/
  εS : ℚ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
