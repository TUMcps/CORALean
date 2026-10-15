module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceGirardCost
public import CORALean.ContSet.Zonotope.Real.Instances

@[expose] public section

/-!
# `LinearSysDT.reachCost`

What running `reach` costs, assembled: one line per operation the step calls,
each line an asserted count from `ContSet/Zonotope/Real/Complexity/Time/`. The only
reading done here is of `reach`'s own definition — three operations per step
and no arithmetic of its own — and the recursion mirrors it line for line.

At `𝒵` and `𝕋 = ℝ`, not at the classes `reach` is written against: `plus` and
`reduce` cost what a representation makes them cost, so a cost is stated where
the instance is. `reach`'s own generality is untouched.

`reachStepBound` is the same three costs at the largest sizes a step can see —
`o * n` generators in, by `Complexity/Space/`'s size facts — and `Theorems/ReachCostLe.lean` is
where the two meet.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `reach` costs over `k` steps at `𝒵`: per step one `mtimes` at the set
it has reached, one `plus`, one `reduce`. -/
noncomputable def LinearSysDT.reachCost (sys : LinearSysDT ℝ n) (o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) : ℕ → Cost
  | 0 => 0
  | k + 1 =>
      sys.reachCost o ho R₀ U k
        + (Zonotope.mtimesCost n n (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).h
            + Zonotope.plusCost n
            + Zonotope.reduceGirardCost n ((sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).h + U.h))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
