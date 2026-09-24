import CORALean.ContDynamics.Reach.Reach
import CORALean.ContDynamics.LinParamSys.Theorems.ReachUnionOuter

/-!
# `LinParamSys ℐ` instantiates `Reach`

`reachExact` is `reachUnionExact`, `reach` is `reachUnion`, and the guarantee
is `reachUnion_outer` — homogeneous, constant-parameter, `U` having no room
in `Params`, exactly `LinearSys`'s instance.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance LinParamSys.reachInstance :
    Reach (LinParamSys ℐ) LinParamSys.ReachParams S where
  reachExact sys p X₀ := sys.reachUnionExact p X₀
  reach sys p X₀ := sys.reachUnion p X₀
  reach_outer sys p X₀ := sys.reachUnion_outer p X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
