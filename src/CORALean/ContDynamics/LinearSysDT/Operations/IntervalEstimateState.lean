module

public import CORALean.ContDynamics.LinearSysDT.Operations.IntervalEstimateStep

@[expose] public section

/-!
# The reachability-based interval estimator's state after `k` steps

[1, Alg. 1], lines 2-3, then lines 8-13 (`intervalEstimateStep`) at `u_k`, `y_k`. Line 2 starts
the estimate at the centre `p₀` of `X₀ = ⟨p₀, H₀⟩` and line 3 the error set at `⟨0, H₀⟩`. Line 3
starts `S_w` and `S_v` at `∅`, which would make line 5's sum empty at every step; they start at
`{0}`, the neutral element of `⊕` that line 5 needs.

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

variable {n nu ny nw nv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.intervalEstimateState (A : Mat ℝ n n) (B : Mat ℝ n nu) (C : Mat ℝ ny n)
    (E : Mat ℝ n nw) (F : Mat ℝ ny nv) (L : Mat ℝ n ny) (X₀ : Zonotope (Vec ℝ n))
    (W : Zonotope (Vec ℝ nw)) (V : Zonotope (Vec ℝ nv)) (u : ℕ → Vec ℝ nu)
    (y : ℕ → Vec ℝ ny) : ℕ → LinearSysDT.IntervalEstimateState n
  | 0 =>
    let x := X₀.c  -- line 2, `x̂₀ = p₀`
    let Dw := Zonotope.mtimes E W  -- line 2, `E W`
    let Dv := Zonotope.mtimes (-(L * F)) V  -- line 2, `-L F V`
    let Sx : Zonotope (Vec ℝ n) := { h := X₀.h, c := 0, G := X₀.G }  -- line 3, `⟨0, H₀⟩`
    let Sw := Interval.point 0  -- line 3
    let Sv := Interval.point 0  -- line 3
    { x := x, Sx := Sx, Sw := Sw, Sv := Sv, Dw := Dw, Dv := Dv }
  | k + 1 => LinearSysDT.intervalEstimateStep A B C L (u k) (y k)
      (LinearSysDT.intervalEstimateState A B C E F L X₀ W V u y k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
