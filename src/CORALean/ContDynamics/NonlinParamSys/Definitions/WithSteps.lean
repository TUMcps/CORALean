import CORALean.ContDynamics.NonlinParamSys.Operations.Augment
import CORALean.ContDynamics.NonlinearSys.Definitions.WithSteps

/-!
# A parametric system, bundled with its augmented `Reach` run

`Reach` runs this class through `augment`, the parameter as `q` states with
zero dynamics, so what a run spends is `NonlinearSys.WithSteps`'s data for the
augmented system in dimension `n + q`: its input set, its chain of
linearizations, their checkable regions and the field bound. `aug_sys` ties
that data to `sys`. The parameter set `P` is bundled beside it, since
`Reach`'s `Params` is one plain `Type` and `P` has dimension `q`, one `Reach`
instance per input dimension `m` and parameter dimension `q`.

The linearizations are of the augmented field, so each certificate already
covers the parameter's uncertainty through the region's last `q` coordinates;
the matrix-set linearization of CORA's `nonlinParamSys`, a `LinParamSys` per
step, is not what is run here.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


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
