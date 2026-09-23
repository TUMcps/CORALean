import CORALean.ContDynamics.NeurNetContrSysDT.Operations
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOrder

/-!
# `NeurNetContrSysDT.reach` bounds the generator count

At `k + 1`, not at `k`, and by the same argument as `LinearSysDT.reach_order_le`:
`reach o R₀ (k + 1)` unfolds to one step of `LinearSysDT.reach`, which ends in
a `reduce`, so `reduce_order_le` bounds it regardless of the controller's own
output size. No induction, and the controller's enclosure never enters.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reachable set after any number of steps has at most `o * n`
generators, at `S := 𝒵`: unfold one step of `reach` and `reduce_order_le`
bounds what it ends in. -/
theorem NeurNetContrSysDT.reach_order_le (sys : NeurNetContrSysDT ℝ 𝒵 n) {o : ℕ} (ho : 0 < o)
    (R₀ : Zonotope (Vec ℝ n)) (k : ℕ) :
    (sys.reach (S := 𝒵) o ho R₀ (k + 1)).h ≤ o * n :=
  Zonotope.reduce_order_le _ ho

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
