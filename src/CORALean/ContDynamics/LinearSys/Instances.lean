import CORALean.ContDynamics.LinearSys.Definitions.ReachParams
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterWindows
import CORALean.ContDynamics.Reach.Reach
import CORALean.ContSet.Interval.Real.Instances

/-!
# `LinearSys` instantiates `Reach`

`reachExact`, `reach` and `reach_outer` are `LinearSys`'s own, at the horizon,
window width and Taylor order `Params` holds — homogeneous only, `U` having no
room in `Params`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   24-September-2026
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
  reachExact sys p X₀ := sys.reachExact p.tFinal X₀
  reach sys p X₀ := sys.reach p.tFinal p.Δt p.η X₀
  reach_outer sys p X₀ := sys.reach_outer p.hΔt X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
