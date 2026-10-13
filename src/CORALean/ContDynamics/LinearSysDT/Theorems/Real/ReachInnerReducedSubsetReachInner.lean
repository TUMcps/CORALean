module

public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInner
public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInnerReduced
public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachErrorReducedContainsReachError

@[expose] public section

/-!
# What reducing the error costs, stated

The two inner approximations differ only in their subtrahend, and
`minkowskiDiff` is antitone there: a point that survives every offset of the
reduced error survives every offset of the unreduced one, which is a subset of
it. So the reduced approximation is the smaller.

Worth stating rather than leaving the two definitions side by side. Soundness
is not what the reduction costs — `reachInnerReduced_inner` is the same claim
as `reachInner_inner` — and without this line a reader has no way to see what
it does cost. It is precision, exactly, and it is the trade the bounded
generator count of `reachErrorReduced_h_le` is bought with.

`subset_` and not `contains`: both sides are `Set`s here, neither a
representation, so the convention that reads a containment off a receiver does
not apply.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reduced inner approximation is contained in the unreduced one: a larger
error taken off leaves less behind. -/
theorem LinearSysDT.reachInnerReduced_subset_reachInner (sys : LinearSysDT ℝ n) {o : ℕ}
    (ho : 0 < o) (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    sys.reachInnerReduced o ho R₀ U k ⊆ sys.reachInner o ho R₀ U k := by
  intro _ hx y hy
  exact hx y (sys.reachErrorReduced_contains_reachError ho R₀ U k hy)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
