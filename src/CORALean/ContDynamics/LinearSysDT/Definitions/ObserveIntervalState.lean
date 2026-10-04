import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.ContSet.Interval.Real.Interval

/-!
# State of the interval observer

CORA's `priv_observe_interval` carries four variables through its loop: the nominal estimate
`x`, the set `R_x` the initial error is mapped to, the box `R_wv` collecting the boxed
disturbance terms, and the disturbance set `D` mapped once more per step.

[1, Alg. 1] carries the same four, `x̂`, `S_x`, `S_wv`, `D`.

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure LinearSysDT.ObserveIntervalState (n : ℕ) where
  x : Vec ℝ n
  Rx : Zonotope (Vec ℝ n)
  Rwv : Interval (Vec ℝ n)
  D : Zonotope (Vec ℝ n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
