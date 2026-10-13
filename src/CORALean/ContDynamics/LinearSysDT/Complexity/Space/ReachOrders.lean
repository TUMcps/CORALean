module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOrder

@[expose] public section

/-!
# `LinearSysDT.reachOrders` bounds the generator count

`reach_order_le` read at the order the sequence supplies for that step: step
`k + 1` unfolds to a `reduce` at `o (k + 1)`, and `reduce_order_le` bounds
what it ends in exactly as it does for `reach`, `ho (k + 1)` taking the place
of the one hypothesis `reach` carries for the whole run.

No induction, for the same reason `reach_order_le` needs none: the bound is a
fact about the last step alone.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) 𝒵]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reachable set after any number of steps has at most `o (k + 1) * n`
generators, at every `S := 𝒵`: the order the sequence supplies for the step
just taken, in place of `reach_order_le`'s one fixed `o`. -/
theorem LinearSysDT.reachOrders_order_le (sys : LinearSysDT 𝕋 n) {o : ℕ → ℕ}
    (ho : ∀ k, 0 < o k) (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    (sys.reachOrders (S := 𝒵) ⟨R₀, U, 0, k + 1⟩ ⟨o, ho⟩).h ≤ o (k + 1) * n :=
  Zonotope.reduce_order_le _ (ho (k + 1))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
