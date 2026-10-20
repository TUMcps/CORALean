module

public import CORALean.ContDynamics.NonlinParamSys.Operations.Augment
public import CORALean.ContDynamics.NonlinearSys.Definitions.WithSteps

@[expose] public section

/-!
# A parametric system, bundled with its augmented `Reach` run

`Reach` runs this class through `augment`, the parameter as `q` states with zero dynamics, so
what a run spends is `NonlinearSys.WithSteps`'s data for the augmented system in dimension
`n + q`: its input set, chain of linearizations, checkable regions and field bound. `aug_sys`
ties that data to `sys`. The parameter set `P`, CORA's `params.paramInt`, is bundled beside it
rather than taken from `params`: the regions cover the parameter's coordinates, so `P` is chosen
with them. The linearizations are of the augmented field; CORA's matrix-set linearization, a
`LinParamSys` per step, is not what is run here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- `sys` with its parameter set `P` and the data a `NonlinearSys.WithSteps` run of
its augmented system `sys.augment` spends, in dimension `n + q`. -/
structure NonlinParamSys.WithSteps (S Rg : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (Rg n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
    [Real.OfInterval S] (m q n : ℕ) where
  sys : NonlinParamSys n m q
  P : S q
  aug : NonlinearSys.WithSteps S Rg m (n + q)
  aug_sys : aug.sys = sys.augment

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
