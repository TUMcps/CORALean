module

public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxOrderSpec
public import CORALean.ContSet.Zonotope.Real.Theorems.StepSubsetClosedBall

@[expose] public section

/-!
# What lets a caller choose the step's order against a stated tolerance

`step_subset_closedBall` leaves the box term a hypothesis; this discharges it
with `reduceBoxOrder`, [1]'s third tuning knob. Pick `o` to be
`reduceBoxOrder` at the caller's own ball of radius `ε` for the pre-reduction
zonotope, and the step lands inside `‖A‖ * r + rU + ε` — a bound the caller
named, not one the reduction happened to produce. This is the missing half
`reduceBoxOrder`'s own docstring named: a width bound to discharge it against,
now supplied.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Choosing the step's order from `reduceBoxOrder` against a caller-stated
tolerance `ε` lands the step inside `‖A‖ * r + rU + ε`. -/
theorem Zonotope.step_subset_closedBall_of_reduceBoxOrder (A : Mat ℝ n n) (hn : 0 < n)
    {Z U : Zonotope (Vec ℝ n)} {r rU ε : ℝ}
    (hZ : Z.construct ⊆ Metric.closedBall (0 : Vec ℝ n) r)
    (hU : U.construct ⊆ Metric.closedBall (0 : Vec ℝ n) rU) (hε : 0 ≤ ε) : -- --- STMT ---
    (Zonotope.reduce (Zonotope.plus (Zonotope.mtimes A Z) U)
        (Zonotope.reduceBoxOrder (Zonotope.plus (Zonotope.mtimes A Z) U)
          (Metric.closedBall (0 : Vec ℝ n) ε))).construct
      ⊆ Metric.closedBall (0 : Vec ℝ n) (‖A‖ * r + rU + ε) := by -- --- PROOF ---
  apply Zonotope.step_subset_closedBall A hZ hU
  exact Zonotope.reduceBoxOrder_spec (Zonotope.plus (Zonotope.mtimes A Z) U) hn
    (Metric.mem_closedBall_self hε)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
