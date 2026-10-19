module

public import CORALean.ContDynamics.NonlinearSysDT.Theorems.HoldsOfReach
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachOuterOfSubset

@[expose] public section

/-!
# `holds_of_reach`, confinement discharged from the computed sets

`holds_of_reach` at `reach_outer_of_subset` in place of `reach_outer`: a caller
checks `hsub` against the concrete sets `reach` builds, instead of assuming
confinement of the trajectory itself. Sound at every `steps` whose regions
pass that check, exactly as `reach_outer_of_subset` is.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {𝕋 : Type} [CORALean.Float.FloatOps 𝕋] [CORALean.Float.SoundFloatArithmetic 𝕋]
variable [Mtimes (Mat 𝕋) S] [CORALean.Float.OfInterval S 𝕋]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.holds_of_reach_of_subset (sys : NonlinearSysDT n m) {U : S m} {o : ℕ}
    (ho : 0 < o) (steps : ℕ → sys.LinStep 𝕋 U) (R₀ : S n)
    (hsub : ∀ k, construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps) ⊆ (steps k).R)
    (spec : Specification ContSet) {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m}
    {y : ℕ → Vec ℝ sys.q} (traj : sys.IsTrajectory R₀ U x u y) (k : ℕ)
    (h : spec.Holds (construct (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps))) : -- --- STMT ---
    spec.Holds {x k} :=
  spec.holds_of_outer
    (Set.singleton_subset_iff.mpr (sys.reach_outer_of_subset ho steps R₀ hsub traj k)) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
