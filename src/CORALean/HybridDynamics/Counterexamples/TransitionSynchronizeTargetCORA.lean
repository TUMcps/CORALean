module

public import CORALean.HybridDynamics.Operations.TransitionSynchronizeTargetCORA

@[expose] public section

/-!
# CORA's synchronized target loop is wrong

CORA's loop on two synchronized transitions (components `0` and `1`, targets `5` and `7`, from
locations `1`, `1`): both components land in location `7`; the components' own targets are `(5,
7)`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's loop gives the last target for both
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Transition


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's loop gives `(7, 7)`, not `(5, 7)`. -/
theorem Transition.synchronizeTargetCORA_counterexample : -- --- CONCL ---
    synchronizeTargetCORA (q := 2) ![1, 1] ![0, 1] ![5, 7] = ![7, 7] ∧
      synchronizeTargetCORA (q := 2) ![1, 1] ![0, 1] ![5, 7] ≠ ![5, 7] := by -- --- PROOF ---
  have h : synchronizeTargetCORA (q := 2) ![1, 1] ![0, 1] ![5, 7] = ![7, 7] := by
    funext c
    fin_cases c <;> simp [synchronizeTargetCORA, List.finRange, Fin.exists_fin_two]
  refine ⟨h, ?_⟩
  rw [h]
  intro h'
  have := congrFun h' 0
  simp at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
