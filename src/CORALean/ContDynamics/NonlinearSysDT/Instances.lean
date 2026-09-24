import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachUnionOuter
import CORALean.ContDynamics.Reach.Reach

/-!
# `NonlinearSysDT.WithSteps` instantiates `Reach`

`reachExact` is `reachUnionExact`, `reach` is `reachUnion`, and the guarantee
is `reachUnion_outer`. `reach` can return `none`, as `NonlinearSys`'s can: each
step's linearization is trusted only once the set it starts from is shown, at
run time, inside that step's region, which is what lets `reach_outer` hold with
no confinement hypothesis on any run.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Real.OfInterval S] [∀ n, Contains (Rg n) (S n)]


-- ========================================  INSTANCES  ========================================= --

instance NonlinearSysDT.reachInstance :
    Reach (NonlinearSysDT.WithSteps S Rg m) NonlinearSysDT.ReachParams S where
  reachExact sys p X₀ := sys.reachUnionExact p X₀
  reach sys p X₀ := sys.reachUnion p X₀
  reach_outer sys p X₀ := sys.reachUnion_outer p X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
