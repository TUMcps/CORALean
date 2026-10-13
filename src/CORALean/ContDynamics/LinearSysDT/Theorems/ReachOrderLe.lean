import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOrder

/-!
# `LinearSysDT.reach` bounds the generator count

At `k + 1`, not at `k`: `reach ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩` ends in a `reduce`, so its size
is bounded regardless of how it got there, and `reduce_order_le` closes it
without touching `k`. At `k = 0` the set is `R₀` itself, the caller's, so there
is nothing to bound.

No induction: the bound is a fact about the last step alone, not about the run.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) 𝒵]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reachable set after any number of steps has at most `o * n`
generators, at every `S := 𝒵`: unfold one step of `reach` and `reduce_order_le`
bounds what it ends in. -/
theorem LinearSysDT.reach_order_le (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    (sys.reach (S := 𝒵) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩).h ≤ o * n :=
  Zonotope.reduce_order_le _ ho

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
