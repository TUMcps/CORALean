import CORALean.ContDynamics.LinParamSysDT.Theorems.HoldsOfReach
import CORALean.Specification.Theorems.CheckSound

/-!
# A passed check on the reachable set holds along every trajectory

`holds_of_reach` with its hypothesis discharged by running `Specification.check` on the
set `reach` computed, through the pair's `Contains` or `IsDisjoint`: a `true`, found by
evaluation, is the specification on the exact state, with nothing left to prove by hand.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.holds_of_check [Contains ContSet (S n)] [IsDisjoint ContSet (S n)]
    (sys : LinParamSysDT 𝕄 n) {o : ℕ} (ho : 0 < o) (R₀ U : S n) (spec : Specification ContSet)
    {x u : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ U x u) (k : ℕ) :
    spec.check (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩) → (spec.Holds {x k}) :=
  fun h => sys.holds_of_reach ho R₀ U spec traj k (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
