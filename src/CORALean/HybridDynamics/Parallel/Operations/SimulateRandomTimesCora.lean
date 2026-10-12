import CORALean.HybridDynamics.Operations.MatlabLinspace

/-!
# The time grid of `parallelHybridAutomaton/simulateRandom`, as CORA writes it

`@parallelHybridAutomaton/simulateRandom.m` (l. 52) draws
`time = linspace(tStart, tFinal, nrConstInp)` and loops `for g = 1:length(time)-1`, where
`@hybridAutomaton/simulateRandom.m` (l. 61) uses `nrConstInp+1`: one constant-input segment too few
(`Theorems.SimulateRandomTimesCoraCounterexample`).
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `time` of `@parallelHybridAutomaton/simulateRandom.m` as printed. -/
def ParallelHybridAutomaton.simulateRandomTimesCora {α : Type} [Field α] (a b : α)
    (nrConstInp : Nat) :
    List α :=
  matlabLinspace a b nrConstInp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
