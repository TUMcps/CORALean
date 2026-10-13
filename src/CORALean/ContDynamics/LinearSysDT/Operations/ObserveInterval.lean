module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalState

@[expose] public section

/-!
# The interval observer

CORA's `priv_observe_interval` with the fixed gain `L`: after `k` loop
iterations, `x + box(R_x) + R_wv`, with the state of `observeIntervalState`. This is the entry
CORA stores as `R{k+2}`: its loop writes `R{i+1}` from the variables before they are updated, so
`R{2}` and `R{1} = R0` both belong to the initial time.

[1, Alg. 1], lines 4-5.

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

open CORALean.Real

variable {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.observeInterval (sys : LinearSysDT ℝ n) (C : Mat ℝ p n) (L : Mat ℝ n p)
    (R₀ W : Zonotope (Vec ℝ n)) (V : Zonotope (Vec ℝ p)) (u : ℕ → Vec ℝ n) (y : ℕ → Vec ℝ p)
    (k : ℕ) : Interval (Vec ℝ n) :=
  let s := sys.observeIntervalState C L R₀ W V u y k
  let E := s.Rx.interval.plus s.Rwv  -- `box(R_x) + R_wv`
  (Interval.point s.x).plus E  -- `x + E`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
