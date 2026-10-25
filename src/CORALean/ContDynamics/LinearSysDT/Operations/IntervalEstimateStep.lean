module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContDynamics.LinearSysDT.Definitions.IntervalEstimateState
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# One step of the reachability-based interval estimator

[1, Alg. 1], lines 8-13, one `let` each, for `x_{k+1} = A x_k + B u_k + E w_k`,
`y_k = C x_k + F v_k` and the observer gain `L`. Real only, as CORA's interval observer
(`aux_observeIntervalStep`) is: no float layer of the observers is written yet.

## Inputs
* `sys` – system
* `L` – observer gain
* `u` – input at this step
* `y` – measurement
* `s` – estimator state

## Output
* the estimator state one step later

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n nu ny : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.intervalEstimateStep (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q) (u : Vec ℝ sys.m)
    (y : Vec ℝ sys.q) (s : LinearSysDT.IntervalEstimateState n) :
    LinearSysDT.IntervalEstimateState n :=
  let x := sys.A *ᵥ s.x + sys.B *ᵥ u + L *ᵥ (y - sys.C *ᵥ s.x)  -- line 8
  let Sx := Zonotope.mtimes (sys.A - L * sys.C) s.Sx  -- line 9
  let Sw := s.Sw.plus s.Dw.interval  -- line 10
  let Sv := s.Sv.plus s.Dv.interval  -- line 11
  let Dw := Zonotope.mtimes (sys.A - L * sys.C) s.Dw  -- line 12
  let Dv := Zonotope.mtimes (sys.A - L * sys.C) s.Dv  -- line 13
  { x := x, Sx := Sx, Sw := Sw, Sv := Sv, Dw := Dw, Dv := Dv }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
