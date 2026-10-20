module

public import CORALean.ContDynamics.LinearSysDT.Complexity.Time.Operations.ReachCost
public import CORALean.ContDynamics.NonlinearSysDT.Operations.Linearize
public import CORALean.ContDynamics.NonlinearSysDT.Operations.LinInput
public import CORALean.ContDynamics.NonlinearSysDT.Operations.Reach
public import CORALean.ContDynamics.NonlinearSysDT.Operations.Simulate
public import CORALean.ContSet.Conversion.Real.Instances

@[expose] public section

/-!
# `NonlinearSysDT.reachCost`

What running `reach` costs, assembled out of a *whole algorithm's* cost rather than leaf
counts: `Operations.lean` runs one step of `LinearSysDT.reach` per linearization, so one step
here is `LinearSysDT.reachCost` at `k = 1`. The only reading done is of `reach`'s own
definition, one call per step with no arithmetic of its own, and the recursion mirrors it. The
linearization is a matrix the caller supplies, so nothing is charged for producing it. At `𝒵`
and `𝕋 = ℝ`, where `LinearSysDT`'s own count is stated.

## Inputs
* `sys` – system
* `U` – input zonotope
* `o` – maximum order
* `steps` – linearization steps
* `R₀` – initial zonotope

## Hypotheses
* `ho` – order positive

## Output
* the cost of the given number of steps
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


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
