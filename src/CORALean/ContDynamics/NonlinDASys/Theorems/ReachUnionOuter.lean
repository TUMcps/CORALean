import CORALean.ContDynamics.NonlinDASys.Operations.ReachUnion
import CORALean.ContDynamics.NonlinDASys.Theorems.ReachUnionExactEq
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachUnionOuter

/-!
# A union `reachUnion` returns contains every state the system reaches

`reachUnionExact_eq` turns the differential-algebraic reachable set into the reduced ordinary
system's, which `NonlinearSys.WithSteps.reachUnion_outer` encloses with no confinement assumed.
It says what the reduced run encloses, given the reduced model; it does not say CORA's
algorithm, which linearizes the differential-algebraic system itself, is sound. The algebraic
part is `ReachYUnionSubsetImage`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m p n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinDASys.WithSteps.reachUnion_outer (sys : NonlinDASys.WithSteps S Rg m p n)
    (params : Reach.Params (S n) ℝ) (options : LinearSys.ReachOptions ℝ) :
    match sys.reachUnion params options with
    | some R => sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀)
        ⊆ construct R
    | none => True := by -- --- PROOF ---
  have h := sys.ode.reachUnion_outer params options
  simp only [NonlinDASys.WithSteps.reachUnion]
  cases hR : sys.ode.reachUnion params options with
  | none => trivial
  | some R =>
    rw [hR] at h
    rw [sys.reachUnionExact_eq]
    exact h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
