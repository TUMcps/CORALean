import CORALean.ContDynamics.NonlinDASys.Definitions.WithSteps
import CORALean.ContDynamics.NonlinearSys.Operations.ReachUnion

/-!
# The reduced re-linearization loop

`NonlinearSys.WithSteps.reachUnion` on the reduced ordinary system, its result unchanged:
the union encloses the states, and the algebraic variables are `h` of them,
`reachYUnion_subset_image`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m p n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ode.reachUnion`, or `none` where the run-time tests of the reduced run fail. -/
noncomputable def NonlinDASys.WithSteps.reachUnion (sys : NonlinDASys.WithSteps S Rg m p n)
    (params : Reach.Params (S n) ℝ) (options : LinearSys.ReachOptions ℝ) :
    Option (SetUnion (S n)) :=
  sys.ode.reachUnion params options

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
