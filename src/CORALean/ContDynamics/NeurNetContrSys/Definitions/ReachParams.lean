import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

/-!
# What `Reach NeurNetContrSys` needs beyond the initial set

`Δt`/`hΔt` are the reachability step, `N` how many make one control period
`N Δt`, `o`/`ho` the maximum order, `H` how many periods `reachUnion` takes.
The Taylor order is not a field — `NeurNetContrSys.reachOrder` derives one
admissible for `Δt` and `sys.plant.A` from both.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The step `Δt` (with `0 < Δt`), the period length `N`, the maximum order
`o` (with `0 < o`) and the period count `H` a `Reach NeurNetContrSys` run is
taken at. -/
structure NeurNetContrSys.ReachParams where
  Δt : ℝ
  hΔt : 0 < Δt
  N : ℕ
  o : ℕ
  ho : 0 < o
  H : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
