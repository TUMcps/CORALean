module

public import CORALean.HybridDynamics.Definitions.IsRunUntil

@[expose] public section

/-!
# A time budget is a bound

A run that fits a budget `T` fits every larger one: the first stay is still no
longer than the budget, and the rest of the run is handed the larger
remainder. So `IsRunUntil T` reads as "lasting at most `T`", not "exactly `T`".

## Inputs
* `HA` – hybrid automaton
* `T` – time budget
* `T'` – larger time budget
* `k` – number of jumps
* `ℓ` – location
* `ℓ'` – end location
* `x` – trajectory of the stay
* `y` – end state

## Hypotheses
* `run` – run within the budget
* `hT` – budget at most the larger budget

## Conclusion
* the run fits the larger budget
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

theorem HybridAutomaton.IsRunUntil.mono {HA : HybridAutomaton S G L 𝕋 n} {T T' : ℝ} {k : ℕ}
    {ℓ ℓ' : L} {x y : Vec ℝ n} (run : HA.IsRunUntil T k ℓ x ℓ' y) (hT : T ≤ T') :
    HA.IsRunUntil T' k ℓ x ℓ' y := by
  induction run generalizing T' with
  | flow h hτ => exact .flow h (hτ.trans hT)
  | jump h hτ hmem hguard _ ih =>
    exact .jump h (hτ.trans hT) hmem hguard (ih (by linarith))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
