import CORALean.ContDynamics.Reach.Reach
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachUnionOuter

/-!
# `LinearSysDT.WithInput` instantiates `Reach`

`reachExact` is `reachUnionExact`, `reach` is `reachUnion`, and the guarantee
is `reachUnion_outer` — nothing new, every field already proved for its own
sake in `Definitions`, `Operations` and `Theorems`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- ========================================  INSTANCES  ========================================= --

instance LinearSysDT.reachInstance :
    Reach (LinearSysDT.WithInput 𝕋 S) LinearSysDT.ReachParams S where
  reachExact sys p X₀ := sys.reachUnionExact p X₀
  reach sys p X₀ := sys.reachUnion p X₀
  reach_outer sys p X₀ := sys.reachUnion_outer p X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
