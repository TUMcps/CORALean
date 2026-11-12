module

public import CORALean.HybridDynamics.Definitions.IsRunUntilDwell

@[expose] public section

/-!
# A run without dwell requirement is a run of `IsRunUntilDwell false`

The runs of `IsRunUntil` and of `IsRunUntilDwell false` are the same, so a result for the latter
holds for every run when the dwell time is not asked for.

## Inputs
* `HA` – hybrid automaton
* `T` – time budget
* `k` – number of jumps
* `ℓ` – start location
* `ℓ'` – end location
* `x` – start state
* `y` – end state

## Hypotheses
* `run` – a run of `IsRunUntil`

## Conclusion
* the same run as one of `IsRunUntilDwell false`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSetLike Scalar

variable {S G : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)] [∀ n, ContSetLike (G n) (Vec ℝ n)]
  {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.IsRunUntil.toDwell {HA : HybridAutomaton S G L 𝕋 n} {T : ℝ} {k : ℕ}
    {ℓ ℓ' : L} {x y : Vec ℝ n} (run : HA.IsRunUntil T k ℓ x ℓ' y) :
    HA.IsRunUntilDwell false T k ℓ x ℓ' y := by
  induction run with
  | flow h hτ => exact .flow h hτ
  | jump h hτ hmem hguard _ ih => exact .jump h hτ (fun hb => absurd hb (by simp)) hmem hguard ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
