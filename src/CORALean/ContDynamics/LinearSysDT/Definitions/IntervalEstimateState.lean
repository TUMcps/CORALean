import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.ContSet.Interval.Real.Interval

/-!
# State of the reachability-based interval estimator

[1, Alg. 1] carries six variables through its loop: the Luenberger estimate `x̂`, the zonotope
`S_x` the initial error is mapped to, the boxes `S_w` and `S_v` collecting the boxed
disturbance and noise terms, and the zonotopes `D_w`, `D_v` mapped once more per step. CORA's
`priv_observe_interval` (`ObserveIntervalState`) is the same with `S_w`, `S_v` and `D_w`, `D_v`
merged.

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

structure LinearSysDT.IntervalEstimateState (n : ℕ) where
  x : Vec ℝ n
  Sx : Zonotope (Vec ℝ n)
  Sw : Interval (Vec ℝ n)
  Sv : Interval (Vec ℝ n)
  Dw : Zonotope (Vec ℝ n)
  Dv : Zonotope (Vec ℝ n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
