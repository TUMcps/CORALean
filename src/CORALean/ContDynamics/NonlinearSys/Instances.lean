import CORALean.ContDynamics.NonlinearSys.Theorems.ReachUnionOuter
import CORALean.ContDynamics.Reach.Reach

/-!
# `NonlinearSys.WithSteps` instantiates `Reach`

`reachExact` is `reachUnionExact`, `reach` is `reachUnion`, and the guarantee
is `reachUnion_outer`. `reach` returns `none` where a step's linearization
could not be trusted: the set it starts from, inflated by `2MΔt`, not shown
inside its region at run time. That test is what lets `reach_outer` hold with
no confinement hypothesis on any run. `ConvexSet` and `CompactSet` are asked of
the representation, as `NeurNetContrSys`'s instance asks them, and discharge
every side condition the linear step would otherwise put in `Params`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance NonlinearSys.reachInstance :
    Reach (NonlinearSys.WithSteps S Rg m) NonlinearSys.ReachParams S where
  reachExact sys p X₀ := sys.reachUnionExact p X₀
  reach sys p X₀ := sys.reachUnion p X₀
  reach_outer sys p X₀ := sys.reachUnion_outer p X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
