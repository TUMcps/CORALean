module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Theorems.StepSubsetClosedBall
public import CORALean.ContSet.Zonotope.Real.Theorems.StepSubsetClosedBallOfReduceBoxOrder

@[expose] public section

/-!
# Closing the loop: `reachOrders` against a tolerance chosen per step

The third obstruction [1]'s tuning left open: `reduceBoxOrder` could be handed a step's zonotope
and a bound and return an order meeting it, but nothing said what that zonotope's box looks like
across a run, so the selector could not be discharged there. `reach_subset_closedBall` answers that
at a *fixed* order, crudely; this is the sharper use `reachOrders` was written for: state the
step's order as `reduceBoxOrder` at a caller-named tolerance `ε`, and the step lands inside
`‖sys.A‖ * r + rU + ε`. What this does not do: choose `ε` itself against a whole-run error the way
[1]'s algorithm does, or carry the bound through `reachOrders`'s own induction into a closed form
over `k` steps, which needs a caller-supplied sequence `ε k` and is a further theorem.

## Inputs
* `sys` – system
* `o` – orders per step
* `R₀` – initial zonotope
* `U` – input zonotope
* `r` – radius of the previous reachable set
* `rU` – radius of the input set
* `ε` – tolerance
* `k` – step

## Hypotheses
* `hn` – dimension positive
* `ho` – orders positive
* `hε` – tolerance nonnegative
* `hR` – previous reachable set lies in its ball
* `hU` – input set lies in its ball
* `heq` – the order is chosen for the tolerance

## Conclusion
* the next reachable set lies in the closed ball of the stated radius

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- If step `k + 1`'s order is `reduceBoxOrder` at the caller's own tolerance
`ε` for that step's pre-reduction zonotope, `reachOrders` lands inside
`‖sys.A‖ * r + rU + ε`. -/
theorem LinearSysDT.reachOrders_step_subset_closedBall_of_reduceBoxOrder (sys : LinearSysDT ℝ n)
    (hn : 0 < n) {o : ℕ → ℕ} (ho : ∀ k, 0 < o k) {R₀ U : Zonotope (Vec ℝ n)}
    {r rU ε : ℝ} (hε : 0 ≤ ε) (k : ℕ)
    (hR : (sys.reachOrders (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct
        ⊆ Metric.closedBall (0 : Vec ℝ n) r)
    (hU : U.construct ⊆ Metric.closedBall (0 : Vec ℝ n) rU)
    (heq : o (k + 1) = Zonotope.reduceBoxOrder
        (Zonotope.plus (Zonotope.mtimes sys.A (sys.reachOrders (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)) U)
        (Metric.closedBall (0 : Vec ℝ n) ε)) : -- --- CONCL ---
    (sys.reachOrders (S := 𝒵) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩).construct
      ⊆ Metric.closedBall (0 : Vec ℝ n) (‖sys.A‖ * r + rU + ε) := by -- --- PROOF ---
  rw [show sys.reachOrders (S := 𝒵) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩
      = Zonotope.reduce
          (Zonotope.plus (Zonotope.mtimes sys.A (sys.reachOrders (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)) U)
          (o (k + 1))
      from rfl, heq]
  exact Zonotope.step_subset_closedBall_of_reduceBoxOrder sys.A hn hR hU hε

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
