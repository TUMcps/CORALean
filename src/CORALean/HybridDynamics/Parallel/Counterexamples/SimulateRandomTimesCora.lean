module

public import CORALean.HybridDynamics.Operations.MatlabLinspace
public import CORALean.HybridDynamics.Operations.SimulateRandomTimes

@[expose] public section

/-!
# The time grid of `parallelHybridAutomaton/simulateRandom`, as CORA writes it

`@parallelHybridAutomaton/simulateRandom.m` (l. 52) draws
`time = linspace(tStart, tFinal, nrConstInp)` and loops `for g = 1:length(time)-1`, where
`@hybridAutomaton/simulateRandom.m` (l. 61) uses `nrConstInp+1`: one constant-input segment too few
(`Theorems.SimulateRandomTimesCoraCounterexample`).

# CORA's parallel `simulateRandom` has one input segment too few

For `nrConstInp = n` the loop `for g = 1:length(time)-1` runs `n - 1` times for the parallel
automaton, `n` times for the hybrid automaton. With `nrConstInp = 1` the parallel automaton
simulates nothing, so every returned trajectory is empty. Read from the source, not run
(`FINDINGS.md`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- `time` of `@parallelHybridAutomaton/simulateRandom.m` as printed. -/
def ParallelHybridAutomaton.simulateRandomTimesCora {α : Type} [Field α] (a b : α)
    (nrConstInp : Nat) :
    List α :=
  matlabLinspace a b nrConstInp


-- =======================================  MAIN THEOREM  ======================================= --

/-- Number of loop iterations: `n - 1` for CORA's parallel grid, `n` for the hybrid automaton's. -/
theorem ParallelHybridAutomaton.simulateRandomTimesCora_segments {α : Type} [Field α]
    (a b : α) (n : Nat) :
    (ParallelHybridAutomaton.simulateRandomTimesCora a b n).length - 1 = n - 1 ∧
      (HybridAutomaton.simulateRandomTimes a b n).length - 1 = n ∧
      (ParallelHybridAutomaton.simulateRandomTimesCora a b 1).length - 1 = 0 := by -- --- PROOF ---
  have len : ∀ m : Nat, (matlabLinspace a b m).length = m := by
    intro m
    unfold matlabLinspace
    by_cases h0 : m = 0
    · simp [h0]
    · by_cases h1 : m = 1
      · simp [h1]
      · simp [h0, h1]
  refine ⟨?_, ?_, ?_⟩
  · simp [ParallelHybridAutomaton.simulateRandomTimesCora, len]
  · simp [HybridAutomaton.simulateRandomTimes, len]
  · simp [ParallelHybridAutomaton.simulateRandomTimesCora, len]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
