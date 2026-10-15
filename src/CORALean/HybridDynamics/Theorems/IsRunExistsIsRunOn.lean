module

public import CORALean.HybridDynamics.HybridAutomaton

@[expose] public section

/-!
# Every run took some number of jumps

The converse of `IsRunOn.toIsRun`: an unbounded run is `IsRunOn k` for the `k` it
happens to have taken, exhibited by the same induction that forgets it. Kept
apart from `toIsRun` since the direction back needs the count, `toIsRun` does not.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.IsRun.exists_isRunOn {HA : HybridAutomaton S G L 𝕋 n} {ℓ ℓ' : L}
    {x y : Vec ℝ n} (run : HA.IsRun ℓ x ℓ' y) : ∃ k, HA.IsRunOn k ℓ x ℓ' y := by
  induction run with
  | flow h => exact ⟨0, .flow h⟩
  | jump h hmem hguard _ ih => exact ⟨ih.choose + 1, .jump h hmem hguard ih.choose_spec⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
