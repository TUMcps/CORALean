import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContDynamics.LinearSysDT.Definitions.ObserveIntervalState
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.Plus
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Interval.Real.Operations.Plus

/-!
# One step of the interval observer

The loop body of CORA's `priv_observe_interval` with the fixed gain `L`:
`x ← A x + B u + L (y - C x)` (the input `u` already in state coordinates, as in
`LinearSysDT`), `R_x ← (A - L C) R_x`, `R_wv ← R_wv + box(D)`, `D ← (A - L C) D`.

[1, Alg. 1], lines 6-9, one `let` each.

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.observeIntervalStep (sys : LinearSysDT ℝ n) (C : Mat ℝ p n) (L : Mat ℝ n p)
    (u : Vec ℝ n) (y : Vec ℝ p) (s : LinearSysDT.ObserveIntervalState n) :
    LinearSysDT.ObserveIntervalState n :=
  let x := sys.A *ᵥ s.x + u + L *ᵥ (y - C *ᵥ s.x)  -- observer update
  let R_x := Zonotope.mtimes (sys.A - L * C) s.Rx  -- initial error through `A - L C`
  let R_wv := s.Rwv.plus s.D.interval  -- add the box of the disturbance term
  let D := Zonotope.mtimes (sys.A - L * C) s.D  -- the disturbance through `A - L C`
  { x := x, Rx := R_x, Rwv := R_wv, D := D }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
