import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuter
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# A specification checked on the reachable set holds along every trajectory

`LinearSysDT.holds_of_reach`'s statement, at a re-linearized step: `reach_outer`
handed to `Specification.holds_of_outer`, so the linearization `steps` and its
confinement hypothesis `hR` are threaded through unchanged rather than hidden
behind a weaker statement. `holds_of_reach_of_subset` is the same corollary
from `hsub`, the check a caller can run against the computed sets instead.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Real.OfInterval S]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.holds_of_reach (sys : NonlinearSysDT n m) {U : S m} {o : ℕ} (ho : 0 < o)
    (steps : ℕ → sys.LinStep U) (R₀ : S n) (spec : Specification ContSet)
    {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m} (traj : sys.Trajectory R₀ U x u)
    (hR : ∀ k, x k ∈ (steps k).R) (k : ℕ)
    (h : spec.Holds (construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps))) : spec.Holds {x k} :=
  spec.holds_of_outer (Set.singleton_subset_iff.mpr (sys.reach_outer ho steps R₀ traj hR k)) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
