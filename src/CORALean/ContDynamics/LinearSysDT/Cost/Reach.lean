import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
import CORALean.ContSet.Zonotope.Real.Cost.API
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# `LinearSysDT.reachCost`

What running `reach` costs, assembled: one line per operation the step calls,
each line an asserted count from `ContSet/Zonotope/Real/Cost/`. The only
reading done here is of `reach`'s own definition — three operations per step
and no arithmetic of its own — and the recursion mirrors it line for line.

At `𝒵` and `𝕋 = ℝ`, not at the classes `reach` is written against: `plus` and
`reduce` cost what a representation makes them cost, so a cost is stated where
the instance is. `reach`'s own generality is untouched.

`reachStepBound` is the same three costs at the largest sizes a step can see —
`o * n` generators in, by `Complexity/`'s size facts — and `ReachBound.lean` is
where the two meet.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


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
        + (Zonotope.mtimesCost n n (sys.reach (S := 𝒵) o ho R₀ U k).h
            + Zonotope.plusCost n
            + Zonotope.reduceGirardCost n ((sys.reach (S := 𝒵) o ho R₀ U k).h + U.h))

/-- The same three costs at a step's worst case: `o * n` generators reaching
the `mtimes`, `o * n + hU` reaching the `reduce`. -/
def LinearSysDT.reachStepBound (n hU o : ℕ) : Cost :=
  Zonotope.mtimesCost n n (o * n) + Zonotope.plusCost n
    + Zonotope.reduceGirardCost n (o * n + hU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
