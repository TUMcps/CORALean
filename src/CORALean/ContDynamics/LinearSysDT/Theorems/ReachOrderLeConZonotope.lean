module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContSet.ConZonotope.Real.Instances
public import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceOrder

@[expose] public section

/-!
# `LinearSysDT.reach` bounds the generator count, at `ConZonotope` too

Word for word `ReachOrderLe.lean`'s argument, because that argument was never
about `Zonotope`: `reach ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩` ends in a `reduce`, whichever
representation runs it, so the bound is a property of the last operation each
step performs, not of what the operation is reducing. Any representation whose
`reduce` bounds its own size — `ConZonotope.reduce_order_le` here — gives the
same conclusion the same way, no induction needed either time.

## Inputs
* `sys` – system
* `o` – maximum order
* `R₀` – initial constrained zonotope
* `U` – input constrained zonotope
* `k` – step

## Hypotheses
* `ho` – order positive

## Conclusion
* the reachable set has at most `o * n` generators
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


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
