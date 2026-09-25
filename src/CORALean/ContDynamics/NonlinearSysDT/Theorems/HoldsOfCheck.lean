import CORALean.ContDynamics.NonlinearSysDT.Theorems.HoldsOfReach
import CORALean.Specification.Theorems.CheckSound

/-!
# A passed check on the reachable set holds along every trajectory

`holds_of_reach` with its hypothesis discharged by running `Specification.check` on the
set `reach` computed, through the pair's `Contains` or `IsDisjoint`: a `true`, found by
evaluation, is the specification on the exact state, with nothing left to prove by hand.
The trajectory still owes `hR`, staying where each step's linearization was certified.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
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

theorem NonlinearSysDT.holds_of_check [Contains ContSet (S n)] [IsDisjoint ContSet (S n)]
    (sys : NonlinearSysDT n m) {U : S m} {o : ℕ} (ho : 0 < o) (steps : ℕ → sys.LinStep U)
    (R₀ : S n) (spec : Specification ContSet) {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m}
    (traj : sys.Trajectory R₀ U x u) (hR : ∀ k, x k ∈ (steps k).R) (k : ℕ) :
    spec.check (sys.reach o ho steps R₀ k) → (spec.Holds {x k}) :=
  fun h => sys.holds_of_reach ho steps R₀ spec traj hR k (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
