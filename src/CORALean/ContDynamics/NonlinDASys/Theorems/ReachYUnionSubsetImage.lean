module

public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.Basic

@[expose] public section

/-!
# The algebraic variables a run reaches lie in `h` of the states and inputs

Every `y t` is `h (x t) (u t)` (`y_eq`), with `x t` in the union `reachUnion` returns
(`reachUnion_outer`) and `u t` in `U`: an outer image of the product, no tighter than `h`
over it.

## Inputs
* `sys` – system with steps
* `params` – reachability parameters
* `options` – reachability options

## Hypotheses
* none

## Conclusion
* the reached algebraic variables lie in the output map's image of the union and inputs
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m p n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinDASys.WithSteps.reachYUnion_subset_image (sys : NonlinDASys.WithSteps S Rg m p n)
    (params : Reach.Params (S n) ℝ) (options : LinearSys.ReachOptions ℝ) : -- --- CONCL ---
    ∀ R ∈ sys.reachUnion params options,
      sys.reachYUnionExact (params.tFinal - params.tStart) (construct params.X₀)
        ⊆ (fun xu : Vec ℝ n × Vec ℝ m => sys.red.h xu.1 xu.2) ''
          (construct R ×ˢ construct sys.ode.U) := by -- --- PROOF ---
  intro R (hR : sys.reachUnion params options = some R)
  have h := sys.reachUnion_outer params options _ hR
  intro z hz
  simp only [NonlinDASys.WithSteps.reachYUnionExact, Set.mem_iUnion, Set.mem_setOf_eq] at hz
  obtain ⟨t, ht, x, y, u, traj, rfl⟩ := hz
  refine ⟨(x t, u t), ⟨h ?_, traj.input t ht⟩, (traj.y_eq sys.red ht).symm⟩
  simp only [NonlinDASys.WithSteps.reachUnionExact, Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨t, ht, x, y, u, traj, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
