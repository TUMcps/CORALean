module

public import CORALean.HybridDynamics.HybridAutomaton

@[expose] public section

/-!
# Forgetting how many jumps a run took

`IsRunOn k` is `IsRun` with its jump count kept alongside; dropping the count is
the identity on the run's own shape, by induction with one case per
constructor, each replayed unchanged under the other family's matching one.

## Inputs
* `HA` – hybrid automaton
* `k` – number of jumps
* `ℓ` – location
* `ℓ'` – end location
* `x` – trajectory of the stay
* `y` – end state

## Hypotheses
* `run` – run of `k` jumps from `x` to `y`

## Conclusion
* the run is a run
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

theorem HybridAutomaton.IsRunOn.toIsRun {HA : HybridAutomaton S G L 𝕋 n} {k : ℕ} {ℓ ℓ' : L}
    {x y : Vec ℝ n} (run : HA.IsRunOn k ℓ x ℓ' y) : HA.IsRun ℓ x ℓ' y := by
  induction run with
  | flow h => exact .flow h
  | jump h hmem hguard _ ih => exact .jump h hmem hguard ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
