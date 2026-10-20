module

public import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorReduced
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOrder

@[expose] public section

/-!
# `LinearSysDT.reachErrorReduced` bounds the generator count

At every `k`, which is where it differs from `reach_order_le`: a step ends in a `reduce`, so
`reduce_order_le` closes it without touching `k`, and at `k = 0` the error is `ofPoint 0` with no
generators at all. `reach` has no such base case — at `k = 0` it is `R₀`, the caller's set, at
whatever order the caller handed over. So the error's description is held at `o * n` throughout.
`reachError` has no bound of this shape: never reducing, it reaches `k * n`. No induction: the
bound is a fact about the last step alone.

## Inputs
* `sys` – system
* `o` – maximum zonotope order
* `R₀` – initial zonotope
* `U` – input zonotope
* `k` – step

## Hypotheses
* `ho` – order positive

## Conclusion
* the reduced error has at most `o * n` generators
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


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
