import CORALean.ContDynamics.Reach.Reach
import CORALean.ContDynamics.LinearSys.Theorems.ReachUnionOuter
import CORALean.ContSet.Interval.Real.Instances

/-!
# `LinearSys` instantiates `Reach`

`reachExact` is `reachUnionExact`, `reach` is `reachUnion`, and the guarantee
is `reachUnion_outer` — homogeneous only, `U` having no room in `Params`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance LinearSys.reachInstance : Reach (LinearSys 𝕋) LinearSys.ReachParams S where
  reachExact sys p X₀ := sys.reachUnionExact p X₀
  reach sys p X₀ := sys.reachUnion p X₀
  reach_outer sys p X₀ := sys.reachUnion_outer p X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
