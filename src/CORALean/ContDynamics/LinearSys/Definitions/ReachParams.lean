import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# What `Reach LinearSys` needs beyond the initial set

Homogeneous only, as `timeIntervalStep` is: `tFinal` is the horizon `[0, tFinal]`,
`Δt` the width of one window and `hΔt` its side condition, `η` the Taylor order
each window is taken at. `η` is a request rather than a promise: `reach` raises it
to `reachOrder`'s order wherever that is higher, since only an order admissible
for `Δt` and `sys.A` makes `timeIntervalStep_outer` hold, and the matrix is not
here to state that as a field.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   24-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The horizon `[0, tFinal]`, covered in windows of width `Δt > 0`, each at
Taylor order `η` or `reachOrder`'s, whichever is higher. -/
structure LinearSys.ReachParams where
  tFinal : ℝ
  Δt : ℝ
  η : ℕ
  hΔt : 0 < Δt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
