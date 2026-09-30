import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

/-!
# CORA's `options` for a continuous closed-loop reach

`timeStep`, the plant's step (CORA's `options.timeStep`), `taylorTerms` and
`zonotopeOrder`. One control period is `N` steps of `timeStep`, CORA's
`sys.dt / options.timeStep`; `N` is the count itself rather than the quotient
because `timeStep : ℝ` feeds `LinearSys.discretize` and no exact quotient exists
there. `hZonotopeOrder` rules out `0`, as in `LinearSysDT.ReachOptions`.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The step `timeStep`, the steps per control period `N`, the Taylor order
`taylorTerms` and the maximum order `zonotopeOrder` (positive). -/
structure NeurNetContrSys.ReachOptions where
  timeStep : ℝ
  N : ℕ
  taylorTerms : ℕ
  zonotopeOrder : ℕ
  hZonotopeOrder : 0 < zonotopeOrder := by exact Nat.zero_lt_succ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
