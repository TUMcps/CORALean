import CORALean.ContDynamics.NonlinearSysDT.Theorems.HoldsOfReach
import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuterOfSubset

/-!
# `holds_of_reach`, confinement discharged from the computed sets

`holds_of_reach` at `reach_outer_of_subset` in place of `reach_outer`: a caller
checks `hsub` against the concrete sets `reach` builds, instead of assuming
confinement of the trajectory itself. Sound at every `steps` whose regions
pass that check, exactly as `reach_outer_of_subset` is.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.holds_of_reach_of_subset (sys : NonlinearSysDT n m) {U : S m} {o : ℕ}
    (ho : 0 < o) (steps : ℕ → sys.LinStep U) (R₀ : S n)
    (hsub : ∀ k, construct (sys.reach o ho steps R₀ k) ⊆ (steps k).R)
    (spec : Specification (Vec ℝ n)) {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m}
    (traj : sys.Trajectory R₀ U x u) (k : ℕ)
    (h : spec.Holds (construct (sys.reach o ho steps R₀ k))) : spec.Holds {x k} :=
  spec.holds_of_outer
    (Set.singleton_subset_iff.mpr (sys.reach_outer_of_subset ho steps R₀ hsub traj k)) h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
