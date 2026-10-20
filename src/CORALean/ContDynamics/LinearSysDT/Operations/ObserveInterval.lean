module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalState
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# The interval observer

CORA's `priv_observe_interval` with the fixed gain `L`: after `k` loop
iterations, `x + box(R_x) + R_wv`, with the state of `observeIntervalState`. This is the entry
CORA stores as `R{k+2}`: its loop writes `R{i+1}` from the variables before they are updated, so
`R{2}` and `R{1} = R0` both belong to the initial time.

[1, Alg. 1], lines 4-5.

## Inputs
* `sys` – system
* `L` – observer gain
* `R₀` – initial zonotope
* `W` – disturbance zonotope
* `V` – noise zonotope
* `u` – inputs
* `y` – measurements
* `k` – step

## Output
* the interval enclosing the state after `k` measurements

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.observeInterval (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (R₀ W : Zonotope (Vec ℝ n)) (V : Zonotope (Vec ℝ sys.q)) (u : ℕ → Vec ℝ sys.m)
    (y : ℕ → Vec ℝ sys.q)
    (k : ℕ) : Interval (Vec ℝ n) :=
  let s := sys.observeIntervalState L R₀ W V u y k
  let E := s.Rx.interval.plus s.Rwv  -- `box(R_x) + R_wv`
  (Interval.point s.x).plus E  -- `x + E`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
