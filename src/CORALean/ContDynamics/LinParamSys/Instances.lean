import CORALean.ContDynamics.LinParamSys.Theorems.ReachUnionOuter
import CORALean.ContDynamics.LinParamSys.Theorems.WithInputReachUnionOuter
import CORALean.ContDynamics.Reach.Reach

/-!
# `LinParamSys ℐ` and `LinParamSys.WithInput` instantiate `Reach`

`reachExact` is `reachUnionExact`, `reach` is `reachUnion` (always `some`: nothing
here can fail at run time), and the guarantee is `reachUnion_outer`, for each —
constant-parameter, over `[0, tFinal]` in `⌈tFinal / Δt⌉` windows, at the point
case's `LinearSys.ReachParams`. `LinParamSys ℐ` is homogeneous;
`LinParamSys.WithInput` carries the input set, `0 ∈ U` among its fields, and
asks the representation to be convex and compact, what `inputSolution`'s
enclosure needs of `U`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   24-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance LinParamSys.reachInstance :
    Reach (LinParamSys ℐ) LinearSys.ReachParams S where
  reachExact sys p X₀ := sys.reachUnionExact p X₀
  reach sys p X₀ := some (sys.reachUnion p X₀)
  reach_outer sys p X₀ := sys.reachUnion_outer p X₀

noncomputable instance LinParamSys.WithInput.reachInstance
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)] :
    Reach (LinParamSys.WithInput S) LinearSys.ReachParams S where
  reachExact sys p X₀ := sys.reachUnionExact p X₀
  reach sys p X₀ := some (sys.reachUnion p X₀)
  reach_outer sys p X₀ := sys.reachUnion_outer p X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
