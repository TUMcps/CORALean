import CORALean.HybridDynamics.HybridAutomaton

/-!
# Forgetting how many jumps a run took

`RunOn k` is `Run` with its jump count kept alongside; dropping the count is
the identity on the run's own shape, by induction with one case per
constructor, each replayed unchanged under the other family's matching one.
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

theorem HybridAutomaton.RunOn.toRun {HA : HybridAutomaton S L 𝕋 n} {k : ℕ} {ℓ ℓ' : L}
    {x y : Vec ℝ n} (run : HA.RunOn k ℓ x ℓ' y) : HA.Run ℓ x ℓ' y := by
  induction run with
  | flow h => exact .flow h
  | jump h hmem hguard _ ih => exact .jump h hmem hguard ih

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
