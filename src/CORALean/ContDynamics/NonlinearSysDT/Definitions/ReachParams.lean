import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT

/-!
# What a `Reach` run of a discrete nonlinear system is taken at

The maximum zonotope order and the step count, exactly `LinearSysDT`'s: a
discrete step needs no window and no Taylor order, and the linearizations the
steps run at are the system's, bundled in `NonlinearSysDT.WithSteps`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The maximum zonotope order `o` (with `0 < o`) and the step count `K` a
`Reach NonlinearSysDT.WithSteps` run is taken at. -/
structure NonlinearSysDT.ReachParams where
  o : ℕ
  ho : 0 < o
  K : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
