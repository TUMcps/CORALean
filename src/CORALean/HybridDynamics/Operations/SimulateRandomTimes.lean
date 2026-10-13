import CORALean.HybridDynamics.Operations.MatlabLinspace

/-!
# The time grid of `hybridAutomaton/simulateRandom`

`@hybridAutomaton/simulateRandom.m` draws `time = linspace(tStart, tFinal, nrConstInp+1)` and
loops `for g = 1:length(time)-1`: `nrConstInp` segments, one per constant input.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `time` of `@hybridAutomaton/simulateRandom.m`. -/
def HybridAutomaton.simulateRandomTimes {α : Type} [Field α] (a b : α) (nrConstInp : Nat) :
    List α :=
  matlabLinspace a b (nrConstInp + 1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
