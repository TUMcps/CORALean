import CORALean.ContDynamics.LinearSysDT.Theorems.ReachStepSubsetClosedBall
import CORALean.ContSet.Zonotope.Real.Theorems.StepSubsetClosedBallOfReduceBoxOrder

/-!
# Closing the loop: `reachOrders` against a tolerance chosen per step

The third obstruction [2]'s tuning left open: `reduceBoxOrder` could be handed
a step's zonotope and a bound and return an order meeting it, but nothing
said what that zonotope's box looks like across a run, so the selector could
not be discharged there. `reach_subset_closedBall` answers that at a *fixed*
order, crudely; this is the sharper use `reachOrders` was written for; state
the step's order as `reduceBoxOrder` at a caller-named tolerance `ε`, and the
step lands inside `‖sys.A‖ * r + rU + ε` — the bound the caller stated, not
one a fixed order happened to produce.

What this does not do: choose `ε` itself against a whole-run error the way
[1]'s algorithm does, or carry this step-by-step bound through
`reachOrders`'s own induction into a closed form over `k` steps — that needs a
caller-supplied sequence `ε k` threaded through `reachOrders`'s order
argument `o`, which is a further theorem, not this one.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
* [2] Issue #32, this morning's notes.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


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
    (hR : (sys.reachOrders (S := 𝒵) o ho R₀ U k).construct
        ⊆ Metric.closedBall (0 : Vec ℝ n) r)
    (hU : U.construct ⊆ Metric.closedBall (0 : Vec ℝ n) rU)
    (heq : o (k + 1) = Zonotope.reduceBoxOrder
        (Zonotope.plus (Zonotope.mtimes sys.A (sys.reachOrders (S := 𝒵) o ho R₀ U k)) U)
        (Metric.closedBall (0 : Vec ℝ n) ε)) :
    (sys.reachOrders (S := 𝒵) o ho R₀ U (k + 1)).construct
      ⊆ Metric.closedBall (0 : Vec ℝ n) (‖sys.A‖ * r + rU + ε) := by -- --- PROOF ---
  rw [show sys.reachOrders (S := 𝒵) o ho R₀ U (k + 1)
      = Zonotope.reduce
          (Zonotope.plus (Zonotope.mtimes sys.A (sys.reachOrders (S := 𝒵) o ho R₀ U k)) U)
          (o (k + 1))
      from rfl, heq]
  exact Zonotope.step_subset_closedBall_of_reduceBoxOrder sys.A hn hR hU hε

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
