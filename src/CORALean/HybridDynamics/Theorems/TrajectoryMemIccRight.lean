module

public import CORALean.HybridDynamics.Definitions.Location

@[expose] public section

/-!
# The dwell time is inside its own interval

`Location.Trajectory.mem_Icc_right`: the state a jump reads, packaged as the
membership the endpoint always has.
-/

-- Authors:       Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The state a jump reads, packaged as the membership the endpoint always has. -/
theorem Location.Trajectory.mem_Icc_right {ℓ : Location S G L 𝕋 n} {τ : ℝ}
    {x : ℝ → Vec ℝ n} {u w} (traj : ℓ.Trajectory τ x u w) : τ ∈ Set.Icc 0 τ :=
  ⟨traj.nonneg, le_refl τ⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
