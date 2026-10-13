module

public import CORALean.HybridDynamics.Operations.UlocCora
public import CORALean.HybridDynamics.Operations.Uloc

@[expose] public section

/-!
# CORA's `uloc` gives locations the wrong input

With `numLoc ≥ 2` locations and the default cell `params.U`, a numeric `params.u` leaves location 0
with the empty input and gives the last location a cell of `numLoc` copies of `u` instead of `u`;
with one location it gives `{u}` instead of `u`. Read from `postProcessing.m` l. 617, not run
(`FINDINGS.md`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.ulocCora_counterexample {α : Type} (numLoc : Nat) (hn : 2 ≤ numLoc)
    (u : α) :
    HybridAutomaton.ulocCora numLoc (numLoc - 1) u 0 = none ∧
      HybridAutomaton.uloc numLoc u 0 = some u ∧
      HybridAutomaton.ulocCora numLoc (numLoc - 1) u (numLoc - 1) =
        some (List.replicate numLoc u) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [HybridAutomaton.ulocCora]; omega
  · simp [HybridAutomaton.uloc]; omega
  · simp [HybridAutomaton.ulocCora]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
