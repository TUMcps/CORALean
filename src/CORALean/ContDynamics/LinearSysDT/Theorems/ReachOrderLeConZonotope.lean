import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
import CORALean.ContSet.ConZonotope.Real.Instances
import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceOrder

/-!
# `LinearSysDT.reach` bounds the generator count, at `ConZonotope` too

Word for word `ReachOrderLe.lean`'s argument, because that argument was never
about `Zonotope`: `reach ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩` ends in a `reduce`, whichever
representation runs it, so the bound is a property of the last operation each
step performs, not of what the operation is reducing. Any representation whose
`reduce` bounds its own size — `ConZonotope.reduce_order_le` here — gives the
same conclusion the same way, no induction needed either time.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) 𝒞]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reachable set after any number of steps has at most `o * n`
generators, at every `S := 𝒞`: unfold one step of `reach` and
`Real.ConZonotope.reduce_order_le` bounds what it ends in. -/
theorem LinearSysDT.reach_order_le_conZonotope (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Real.ConZonotope (Vec ℝ n)) (k : ℕ) :
    (sys.reach (S := 𝒞) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩).h ≤ o * n :=
  Real.ConZonotope.reduce_order_le _ ho

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
