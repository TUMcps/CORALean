module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContSet.ConZonotope.Real.Instances
public import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceOrder

@[expose] public section

/-!
# `LinearSysDT.reach` bounds the degree-of-freedom order, at `ConZonotope` too

`ReachOrderLe.lean`'s argument at `ConZonotope`: `reach ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩` ends in a
`reduce`, so the bound is a property of the last operation each step performs. CORA's
`conZonotope/reduce` brings the degree-of-freedom order to `o`, not the generator count: at most
`o n` generators beyond the equality rows (`ConZonotope.reduce_order_le`). The equality rows
themselves are not reduced, and every `plus` of the input adds its own, so the generator count
alone is not bounded here.

## Inputs
* `sys` – system
* `o` – maximum order
* `R₀` – initial constrained zonotope
* `U` – input constrained zonotope
* `k` – step

## Hypotheses
* `ho` – order positive

## Conclusion
* the reachable set has at most `o * n` generators beyond its equality rows
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) 𝒞]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reachable set after any number of steps has at most `o * n` generators beyond its
equality rows, at every `S := 𝒞`: `Real.ConZonotope.reduce_order_le` bounds what a step ends in. -/
theorem LinearSysDT.reach_order_le_conZonotope (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Real.ConZonotope (Vec ℝ n)) (k : ℕ) :
    (sys.reach (S := 𝒞) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩).h
      ≤ o * n + (sys.reach (S := 𝒞) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩).P.me :=
  Real.ConZonotope.reduce_order_le _ ho

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
