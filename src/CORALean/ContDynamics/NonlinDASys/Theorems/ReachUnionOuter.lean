module

public import CORALean.ContDynamics.NonlinDASys.Operations.ReachUnion
public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachUnionExactEq
public import CORALean.ContDynamics.NonlinearSys.Theorems.ReachUnionOuter

@[expose] public section

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
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


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
    (params : Reach.Params (S n) ℝ) (options : LinearSys.ReachOptions ℝ)
    {R : SetUnion (S n)} (hR : sys.reachUnion params options = some R) : -- --- STMT ---
    sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀)
      ⊆ construct R := by -- --- PROOF ---
  -- the run is the reduced one, and so is the set it reaches
  rw [sys.reachUnionExact_eq]
  exact sys.ode.reachUnion_outer params options hR

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
