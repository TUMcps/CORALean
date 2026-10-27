module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# State of the reachability-based interval estimator

[1, Alg. 1] carries six variables through its loop: the Luenberger estimate `x̂`, the zonotope
`S_x` the initial error is mapped to, the boxes `S_w` and `S_v` collecting the boxed
disturbance and noise terms, and the zonotopes `D_w`, `D_v` mapped once more per step. CORA's
`priv_observe_interval` (`ObserveIntervalState`) is the same with `S_w`, `S_v` and `D_w`, `D_v`
merged.

## References

* [1] [W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      2019.](../../../../../references/2019/tang-tac-interval-estimation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- The state of the reachability-based interval estimator: the point estimate `x`, the estimate set
`Sx`, the disturbance and noise intervals `Sw`, `Sv`, and their zonotope parts `Dw`, `Dv`. -/
structure LinearSysDT.IntervalEstimateState (n : ℕ) where
  x : Vec ℝ n
  Sx : Zonotope (Vec ℝ n)
  Sw : Interval (Vec ℝ n)
  Sv : Interval (Vec ℝ n)
  Dw : Zonotope (Vec ℝ n)
  Dv : Zonotope (Vec ℝ n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
