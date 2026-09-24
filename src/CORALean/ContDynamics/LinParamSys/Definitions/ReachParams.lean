import CORALean.ContDynamics.LinParamSys.LinParamSys

/-!
# What `Reach (LinParamSys ℐ)` needs beyond the initial set

Homogeneous only, as `timeIntervalStep` is, and constant-parameter, as its
`ConstTrajectory` guarantee is: `r` is the window `[0, r]` `reachUnion` is
taken over in one step, `hr` its side condition. `LinearSys.reachOrder`'s
matrix norm is `(Interval.smul r sys.A).absMax` here, the interval matrix's
own — which is again all `reach_outer` needs beyond `sys`, `p` and `X₀`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The window `[0, r]` (with `0 < r`) a `Reach (LinParamSys ℐ)` run is taken
over, in one step. -/
structure LinParamSys.ReachParams where
  r : ℝ
  hr : 0 < r

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
