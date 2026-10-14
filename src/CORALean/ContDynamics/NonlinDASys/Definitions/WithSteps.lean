module

public import CORALean.ContDynamics.NonlinDASys.Operations.Basic
public import CORALean.ContDynamics.NonlinearSys.Definitions.WithSteps

@[expose] public section

/-!
# A differential-algebraic system, bundled with its reduced `Reach` run

`Reach` runs this class through its reduced model: `ode` is `NonlinearSys.WithSteps`'s data
for the ordinary system `red.toNonlinearSys` (input set, chain of linearizations, checkable
regions, field bound), and `ode_sys` ties it to `sys`. This is not CORA's algorithm, which
linearizes the differential-algebraic system itself and carries an error term for the
algebraic variable; it is the run available once `y` has been eliminated, and it needs
the reduced model `red` as data. One `Reach` instance per input dimension `m` and constraint
dimension `p`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Real.OfInterval S]
variable {m p n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- `sys` with a reduced model `red` and the data a `NonlinearSys.WithSteps` run of the
reduced ordinary system spends. -/
structure NonlinDASys.WithSteps (S Rg : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (Rg n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
    [Real.OfInterval S] (m p n : ℕ) where
  sys : NonlinDASys n p m
  red : sys.ReducedModel
  ode : NonlinearSys.WithSteps S Rg m n
  ode_sys : ode.sys = red.toNonlinearSys

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
