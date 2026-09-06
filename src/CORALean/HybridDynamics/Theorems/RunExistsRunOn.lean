import CORALean.HybridDynamics.HybridAutomaton

/-!
# Every run took some number of jumps

The converse of `RunOn.toRun`: an unbounded run is `RunOn k` for the `k` it
happens to have taken, exhibited by the same induction that forgets it. Kept
apart from `toRun` since the direction back needs the count, `toRun` does not.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet Scalar

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.Run.exists_runOn {HA : HybridAutomaton S L 𝕋 n} {ℓ ℓ' : L}
    {x y : Vec ℝ n} (run : HA.Run ℓ x ℓ' y) : ∃ k, HA.RunOn k ℓ x ℓ' y := by
  induction run with
  | flow h => exact ⟨0, .flow h⟩
  | jump h hmem hguard _ ih => exact ⟨ih.choose + 1, .jump h hmem hguard ih.choose_spec⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
