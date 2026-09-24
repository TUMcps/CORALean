import CORALean.ContDynamics.NonlinearSysDT.Definitions.LinStep

/-!
# A discrete nonlinear system, bundled with what its `Reach` run spends

`Reach.Params` is one plain `Type`, not indexed by `n`, so it cannot hold the
input set `U`, the chain of linearizations `steps` or anything else of one
dimension; they are bundled with the system instead, as
`LinearSysDT.WithInput` bundles `U`. The input dimension `m` is a parameter of
the bundle, so each `m` is one `Reach` instance.

`(steps i).R` is an arbitrary set, which nothing can test containment in, so
the bundle also carries `region i`, a representation whose `Contains` can run,
inside `(steps i).R`. `reach` checks against `region i` and proves against
`(steps i).R`; `region_subset` is what connects the two.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- `sys` with its input set `U`, a chain of linearizations `steps`, and for
each step a checkable region inside the one its certificate was issued for. -/
structure NonlinearSysDT.WithSteps (S Rg : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (Rg n) (Vec ℝ n)] (m n : ℕ) where
  sys : NonlinearSysDT n m
  U : S m
  steps : ℕ → sys.LinStep U
  region : ℕ → Rg n
  region_subset (i : ℕ) : construct (region i) ⊆ (steps i).R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
