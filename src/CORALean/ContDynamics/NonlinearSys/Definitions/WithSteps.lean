module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinStepLinInput

@[expose] public section

/-!
# A nonlinear system, bundled with what its `Reach` run spends

Each step's certificate `steps i` is issued for the input set `U`, its type
depends on it, so `U` is bundled with the system and the chain rather than taken
from CORA's `params.U`, as in `NonlinearSysDT.WithSteps`, one `Reach` instance per
input dimension `m`. `region i` is a representation `Contains` can test,
inside the arbitrary set `(steps i).R` step `i`'s certificate was issued for.

`M` bounds the field over every certified region, the a priori bound
`confined_of_ball` spends: a run cannot move farther than `MΔt` in one step, so
a region that holds a ball of radius `2MΔt` about every state a step starts
from holds the whole step. `0 ∈ linInput` is `timeInterval_outer`'s own price.
Neither involves the step width or the horizon, `options` and `params`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- `sys` with its input set `U`, a chain of linearizations `steps`, for each step
a checkable region inside its certified one, and a bound `M` on the field there. -/
structure NonlinearSys.WithSteps (S Rg : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (Rg n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
    [Real.OfInterval S] (m n : ℕ) where
  sys : NonlinearSys n m
  U : S m
  steps : ℕ → sys.LinStep U
  region : ℕ → Rg n
  region_subset (i : ℕ) : construct (region i) ⊆ (steps i).R
  M : ℝ
  M_pos : 0 < M
  norm_f_le (i : ℕ) : ∀ y ∈ (steps i).R, ∀ v ∈ construct U, ‖sys.f y v‖ ≤ M
  zero_mem_linInput (i : ℕ) : (0 : Vec ℝ n) ∈ construct (steps i).linInput

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
