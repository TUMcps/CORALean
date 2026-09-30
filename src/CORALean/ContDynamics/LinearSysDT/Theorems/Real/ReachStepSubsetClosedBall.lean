import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Theorems.StepSubsetClosedBall

/-!
# One step of `reach` bounds the sup-norm ball it lands in

`Zonotope.step_subset_closedBall` read at the step `reach` actually takes:
`mtimes` by the system matrix, `plus` with the input set, `reduce` at the
fixed order the whole run shares. `‖sys.A‖` is the `l∞` operator norm — the
one already local-instanced throughout `LinearSys`, `LinParamSys` and
`MatExp` — and `Vec ℝ n`'s norm is the sup norm it pairs with, so no new norm
enters here.

`_step_`, not `_le`: this is the analogue of `reach_order_le` for the set's
reach rather than its generator count, one step at a time and no induction —
`reach_subset_closedBall` is where the steps compose into a run.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Step `k + 1` of `reach` reaches no further than `‖sys.A‖ * r + rU + rbox`,
given a ball for the state reached at step `k`, one for `U`, and one for the
box that step's own reduction pays. -/
theorem LinearSysDT.reach_step_subset_closedBall (sys : LinearSysDT ℝ n) {o : ℕ} (ho : 0 < o)
    {R₀ U : Zonotope (Vec ℝ n)} {r rU rbox : ℝ} (k : ℕ)
    (hR : (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct ⊆ Metric.closedBall (0 : Vec ℝ n) r)
    (hU : U.construct ⊆ Metric.closedBall (0 : Vec ℝ n) rU)
    (hbox : (((Zonotope.mtimes sys.A
        (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)).plus U).reduceBox o).construct
        ⊆ Metric.closedBall (0 : Vec ℝ n) rbox) :
    (sys.reach (S := 𝒵) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩).construct
      ⊆ Metric.closedBall (0 : Vec ℝ n) (‖sys.A‖ * r + rU + rbox) :=
  Zonotope.step_subset_closedBall sys.A hR hU hbox

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
