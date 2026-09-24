import CORALean.ContDynamics.NonlinParamSys.Theorems.ReachUnionOuter
import CORALean.ContDynamics.Reach.Reach

/-!
# `NonlinParamSys.WithSteps` instantiates `Reach`

`reachExact` is `reachUnionExact`, the constant-parameter reachable set; `reach`
is `reachUnion`, the augmented-state run projected back; the guarantee is
`reachUnion_outer`. `reach` returns `none` exactly where the augmented
`NonlinearSys.WithSteps` run does: some step's start, inflated by `2MΔt`, not
shown inside its region, which is tested in dimension `n + q`, the parameter's
coordinates with the state's. `Params` is `NonlinearSys.ReachParams`, the
augmented run's own; `ConvexSet` and `CompactSet` are asked of the
representation for the same reason as there.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m q : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance NonlinParamSys.reachInstance :
    Reach (NonlinParamSys.WithSteps S Rg m q) NonlinearSys.ReachParams S where
  reachExact sys p X₀ := sys.reachUnionExact p X₀
  reach sys p X₀ := sys.reachUnion p X₀
  reach_outer sys p X₀ := sys.reachUnion_outer p X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
