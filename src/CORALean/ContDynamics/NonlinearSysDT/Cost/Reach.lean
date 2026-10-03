import CORALean.ContDynamics.LinearSysDT.Cost.Reach
import CORALean.ContDynamics.NonlinearSysDT.Operations.Linearize
import CORALean.ContDynamics.NonlinearSysDT.Operations.LinInput
import CORALean.ContDynamics.NonlinearSysDT.Operations.Reach
import CORALean.ContDynamics.NonlinearSysDT.Operations.Simulate
import CORALean.ContSet.Conversion.Real.Interval_to_ContSet

/-!
# `NonlinearSysDT.reachCost`

What running `reach` costs, assembled, and assembled out of a *whole
algorithm's* cost rather than out of leaf counts: `Operations.lean` runs one
step of `LinearSysDT.reach` per linearization, so one step here is
`LinearSysDT.reachCost` at `k = 1` and this file reads nothing else off.

The only reading done is of `reach`'s own definition — one call per step, no
arithmetic of its own — and the recursion mirrors it line for line. The
linearization is a matrix the caller supplies, not one this operation computes,
so nothing is charged for producing it; a caller who computes a Jacobian pays
for that where it is computed.

At `𝒵` and `𝕋 = ℝ`, where `LinearSysDT`'s own count is stated, and for the same
reason: `plus` and `reduce` cost what a representation makes them cost.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `reach` costs over `k` re-linearized steps at `𝒵`: per step one step
of the linear run, at that step's own matrix and its own input set. -/
noncomputable def NonlinearSysDT.reachCost (sys : NonlinearSysDT n m)
    {U : Zonotope (Vec ℝ m)} (o : ℕ) (ho : 0 < o) (steps : ℕ → sys.LinStep ℝ (S := 𝒵) U)
    (R₀ : Zonotope (Vec ℝ n)) : ℕ → Cost
  | 0 => 0
  | k + 1 =>
      sys.reachCost o ho steps R₀ k
        + (NonlinearSysDT.linearize (steps k).A).reachCost o ho
            (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps) (steps k).linInput 1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
