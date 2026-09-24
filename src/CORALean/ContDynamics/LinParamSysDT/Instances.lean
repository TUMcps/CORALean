import CORALean.ContDynamics.Reach.Reach
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachUnionOuter

/-!
# `LinParamSysDT.WithInput` instantiates `Reach`

`reachExact` is `reachUnionExact`, `reach` is `reachUnion` (always `some`: nothing
here can fail at run time), and the guarantee
is `reachUnion_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- ========================================  INSTANCES  ========================================= --

instance LinParamSysDT.reachInstance :
    Reach (LinParamSysDT.WithInput 𝕄 S) LinParamSysDT.ReachParams S where
  reachExact sys p X₀ := sys.reachUnionExact p X₀
  reach sys p X₀ := some (sys.reachUnion p X₀)
  reach_outer sys p X₀ _ h := Option.mem_some_iff.mp h ▸ sys.reachUnion_outer p X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
