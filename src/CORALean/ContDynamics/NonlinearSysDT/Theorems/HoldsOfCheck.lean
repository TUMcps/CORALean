module

public import CORALean.ContDynamics.NonlinearSysDT.Theorems.HoldsOfReach
public import CORALean.Specification.Theorems.CheckSound

@[expose] public section

/-!
# A passed check on the reachable set holds along every trajectory

`holds_of_reach` with its hypothesis discharged by running `Specification.check` on the
set `reach` computed, through the pair's `Contains` or `IsDisjoint`: a `true`, found by
evaluation, is the specification on the exact state, with nothing left to prove by hand.
The trajectory still owes `hR`, staying where each step's linearization was certified.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
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

theorem NonlinearSysDT.holds_of_check [Contains ContSet (S n)] [IsDisjoint ContSet (S n)]
    (sys : NonlinearSysDT n m) {U : S m} {o : ℕ} (ho : 0 < o) (steps : ℕ → sys.LinStep 𝕋 U)
    (R₀ : S n) (spec : Specification ContSet) {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m}
    {y : ℕ → Vec ℝ sys.q} (traj : sys.IsTrajectory R₀ U x u y) (hR : ∀ k, x k ∈ (steps k).R)
    (k : ℕ) : -- --- CONCL ---
    spec.check (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ steps) → (spec.Holds {x k}) :=
  fun h => sys.holds_of_reach ho steps R₀ spec traj hR k (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
