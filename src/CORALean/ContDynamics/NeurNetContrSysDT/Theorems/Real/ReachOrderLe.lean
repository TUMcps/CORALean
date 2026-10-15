module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Reach
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOrder

@[expose] public section

/-!
# `NeurNetContrSysDT.reach` bounds the generator count

At `k + 1`, not at `k`, and by the same argument as `LinearSysDT.reach_order_le`:
`reach o R₀ (k + 1)` unfolds to one step of `LinearSysDT.reach`, which ends in
a `reduce`, so `reduce_order_le` bounds it regardless of the controller's own
output size and of the external inputs'. No induction, and the controller's enclosure never enters.
-/

-- Authors:       Claude Sonnet 5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reachable set after any number of steps has at most `o * n`
generators, at `S := 𝒵`: unfold one step of `reach` and `reduce_order_le`
bounds what it ends in. -/
theorem NeurNetContrSysDT.reach_order_le (sys : NeurNetContrSysDT (LinearSysDT ℝ n) 𝒵 n) {o : ℕ}
    (U_ext : Zonotope (Vec ℝ sys.nExt)) (ho : 0 < o)
    (R₀ : Zonotope (Vec ℝ n)) (k : ℕ) :
    (sys.reach (S := 𝒵) U_ext ⟨R₀, 0, k + 1⟩ ⟨o, ho⟩).h ≤ o * n :=
  Zonotope.reduce_order_le _ ho

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
