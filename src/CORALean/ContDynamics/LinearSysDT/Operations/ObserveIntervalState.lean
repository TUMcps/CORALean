module

public import CORALean.ContDynamics.LinearSysDT.Definitions.ObserveIntervalState
public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Point
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# The interval observer's state after `k` steps

CORA's `priv_observe_interval` initialisation, `x = center(R0)`, `R_x = R0`, `R_wv = 0`,
`D = -L V + W`, then `aux_observeIntervalStep` at the measurement `y k` and input `u k`.

[1, Alg. 1], lines 1-2 and the loop.

## Inputs
* `sys` – system
* `L` – observer gain
* `R₀` – initial zonotope
* `W` – disturbance zonotope
* `V` – noise zonotope
* `u` – inputs
* `y` – measurements

## Output
* the observer state after each number of steps

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". 8th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH21), 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n p : ℕ}
open Matrix CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def LinearSysDT.aux_observeIntervalStep (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (u : Vec ℝ sys.m) (y : Vec ℝ sys.q) (s : LinearSysDT.ObserveIntervalState n) :
    LinearSysDT.ObserveIntervalState n :=
  let x := sys.A *ᵥ s.x + sys.B *ᵥ u + L *ᵥ (y - sys.C *ᵥ s.x)  -- observer update
  let R_x := Zonotope.mtimes (sys.A - L * sys.C) s.Rx  -- initial error through `A - L C`
  let R_wv := s.Rwv.plus s.D.interval  -- add the box of the disturbance term
  let D := Zonotope.mtimes (sys.A - L * sys.C) s.D  -- the disturbance through `A - L C`
  { x := x, Rx := R_x, Rwv := R_wv, D := D }


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.observeIntervalState (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (R₀ W : Zonotope (Vec ℝ n)) (V : Zonotope (Vec ℝ sys.q)) (u : ℕ → Vec ℝ sys.m)
    (y : ℕ → Vec ℝ sys.q) :
    ℕ → LinearSysDT.ObserveIntervalState n
  | 0 => { x := R₀.c, Rx := R₀, Rwv := Interval.point 0, D := (Zonotope.mtimes (-L) V).plus W }
  | k + 1 => sys.aux_observeIntervalStep L (u k) (y k) (sys.observeIntervalState L R₀ W V u y k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
