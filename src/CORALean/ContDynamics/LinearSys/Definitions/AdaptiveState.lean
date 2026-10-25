module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Alg. 1`'s loop state, in floats

`AdaptiveState`: what one iteration of [1, Alg. 1] hands the next when it runs
in `𝕋`. The time `t_i` is kept twice: exactly in ℚ, the sum of the steps
read back through `ToRat`, and as a float bracket `tEnc` for the
enclosure of `e^{A t_i}`, rounded outward step by step.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- What one iteration of [1, Alg. 1] hands the next, in `𝕋`. -/
structure LinearSys.AdaptiveState (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) where
  /-- `t_i`, line 10, relative to `tStart`. -/
  t : ℚ
  /-- A bracket of floats around `t_i`. -/
  tEnc : Interval 𝕋
  /-- `Δt_{i-1}`, the step `Alg. 2` enlarges at its own line 1. -/
  Δt : 𝕋
  /-- `ε_P([0,t_i])`, eq. (9). -/
  εP : ℚ
  /-- `ε_S([0,t_i])`, eq. (12). -/
  εS : ℚ
  /-- `P̃(t_i) ⊕ PR([0,t_i])`, the constant and the varying input's share by `t_i`. -/
  P : Zonotope (Vec 𝕋 n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
