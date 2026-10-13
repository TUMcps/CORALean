module

public import CORALean.HybridDynamics.Definitions.RunUntil

@[expose] public section

/-!
# A run of bounded duration is a run

Forgetting the time budget: every `RunUntil` is the `RunOn` with the same
stays and jumps, so a guarantee stated over `RunUntil` speaks of runs of the
automaton and nothing weaker.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.RunUntil.toRunOn {HA : HybridAutomaton S G L 𝕋 n} {T : ℝ} {k : ℕ}
    {ℓ ℓ' : L} {x y : Vec ℝ n} (run : HA.RunUntil T k ℓ x ℓ' y) : HA.RunOn k ℓ x ℓ' y := by
  induction run with
  | flow h => exact .flow h
  | jump h _ hmem hguard _ ih => exact .jump h hmem hguard ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
