import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorReduced
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOrder

/-!
# `LinearSysDT.reachErrorReduced` bounds the generator count

At every `k`, which is the point of the definition and where it differs from
`reach_order_le`: a step ends in a `reduce`, so `reduce_order_le` closes it
without touching `k`, and at `k = 0` the error is `ofPoint 0` with no
generators at all. `reach` has no such base case — at `k = 0` it is `R₀`, the
caller's set, at whatever order the caller handed over.

So the error's description is held at `o * n` throughout, the same bound the
run itself meets from the first step on. `reachError` has no bound of this
shape: never reducing, it grows a box per step and reaches `k * n`.

No induction: the bound is a fact about the last step alone.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reduced error has at most `o * n` generators after any number of
steps — the origin at `k = 0`, and a `reduce` at every step after. -/
theorem LinearSysDT.reachErrorReduced_h_le (sys : LinearSysDT ℝ n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    (sys.reachErrorReduced ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).h ≤ o * n := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k => exact Zonotope.reduce_order_le _ ho

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
