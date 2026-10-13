import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

/-!
# CORA's `options` for a continuous closed-loop reach

`Δt`, the plant's step (CORA's `options.timeStep`), `η` and
`ρ`. One control period is `N` steps of `Δt`, CORA's
`sys.dt / options.Δt`; `N` is the count itself rather than the quotient
because `Δt` feeds `LinearSys.discretize` and no exact quotient exists
there. `hZonotopeOrder` rules out `0`, as in `LinearSysDT.ReachOptions`. `τ` is
the time type, `ℝ` for `reach` and the float scalar for `reachFloat`, as in
`LinearSys.ReachOptions`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       30-September-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The step `Δt`, the steps per control period `N`, the Taylor order
`η` and the maximum order `ρ` (positive). -/
structure NeurNetContrSys.ReachOptions (τ : Type) where
  Δt : τ
  N : ℕ
  η : ℕ
  ρ : ℕ
  hZonotopeOrder : 0 < ρ := by exact Nat.zero_lt_succ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
