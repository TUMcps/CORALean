module

public import CORALean.HybridDynamics.Definitions.Transition

@[expose] public section

/-!
# `Transition.synchronizeTarget`

The target tuple of CORA's `transition/synchronize`: `locID` with component `compIdx i` moved to
the target of transition `i`. The targets are typed by the component (`L (compIdx i)`), so the
component is `compIdx i`, which CORA's loop does not use (`Transition.synchronizeTargetCORA`,
`FINDINGS.md`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {k q : ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The target tuple: `locID`, with component `compIdx i` moved to the target of transition `i`. -/
def Transition.synchronizeTarget (locID : ∀ c, L c) (compIdx : Fin q → Fin k)
    (target : ∀ i, L (compIdx i)) : ∀ c, L c :=
  (List.finRange q).foldl (fun t i => Function.update t (compIdx i) (target i)) locID

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
