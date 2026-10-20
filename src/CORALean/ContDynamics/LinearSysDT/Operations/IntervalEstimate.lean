module

public import CORALean.ContDynamics.LinearSysDT.Operations.IntervalEstimateState
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# The reachability-based interval estimator

[1, Alg. 1], lines 5-7: after `k` steps the box `[x̲_k, x̅_k] = x̂_k + [e̲_k, e̅_k]`, with
`[e̲_k, e̅_k] = Box(S_x) ⊕ S_w ⊕ S_v`, the state of `intervalEstimateState`. The box of `S_x`
is `Zonotope.interval`, exact by [1, Property 4] (`Zonotope.interval_eq_hull`).

## Inputs
* `sys` – system
* `L` – observer gain
* `X₀` – initial zonotope
* `W` – disturbance zonotope
* `V` – noise zonotope
* `u` – inputs
* `y` – measurements
* `k` – step

## Output
* the interval estimate of the state after `k` steps

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n nu ny nw nv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.intervalEstimate (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (X₀ : Zonotope (Vec ℝ n))
    (W : Zonotope (Vec ℝ sys.r)) (V : Zonotope (Vec ℝ sys.s)) (u : ℕ → Vec ℝ sys.m)
    (y : ℕ → Vec ℝ sys.q) (k : ℕ) : Interval (Vec ℝ n) :=
  let s := LinearSysDT.intervalEstimateState sys L X₀ W V u y k
  let e := s.Sx.interval.plus (s.Sw.plus s.Sv)  -- line 5, `[e̲_k, e̅_k]`
  (Interval.point s.x).plus e  -- lines 6-7, `x̂_k + [e̲_k, e̅_k]`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
