module

public import CORALean.HybridDynamics.Definitions.Transition

@[expose] public section

/-!
# `Transition.synchronizeTargetCORA`

CORA's target loop of `transition/synchronize`, transcribed literally, locations being numbers as
in CORA: `target(compIdx) = transList(i).target` writes the target of transition `i` to every
participating component, so the last one wins. Kept to state the counterexample.

## Inputs
* `locID` – current locations
* `compIdx` – component indices
* `target` – target locations

## Output
* locations as CORA's loop sets them
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {k q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's loop, literally: the target of transition `i` goes to *every* entry of `compIdx`. -/
def Transition.synchronizeTargetCORA (locID : Fin k → ℕ) (compIdx : Fin q → Fin k)
    (target : Fin q → ℕ) : Fin k → ℕ :=
  (List.finRange q).foldl
    (fun t i => fun c => if ∃ j, compIdx j = c then target i else t c) locID

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
