module

public import CORALean.ContDynamics.LinearSys.Definitions.TunedState

@[expose] public section

/-!
# `Alg. 1` lines 1-3: the loop state before the first iteration

`tunedInit`: [1, Alg. 1] lines 1-3, the time, the step `Alg. 2` starts from, and the two
accumulated errors, before the first iteration.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 1-3: the time, the step `Alg. 2` starts from, and the two accumulated
errors, before the first iteration. -/
noncomputable def LinearSys.tunedInit (tf μ : ℝ) : LinearSys.TunedState n :=
  { t := 0                                                       -- 1. t ← 0
    Δt := tf * μ                                                  -- 2. Δt₋₁ ← t_f μ
    η := 0
    εP := 0                                                       -- 3. ε_P([0,0]) ← 0
    εS := 0                                                       -- 3. ε_S([0,0]) ← 0
    PR := Zonotope.ofPoint 0
    R := Zonotope.ofPoint 0 }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
