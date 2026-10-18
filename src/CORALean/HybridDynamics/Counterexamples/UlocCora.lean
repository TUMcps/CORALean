module

public import CORALean.HybridDynamics.Operations.Basic

@[expose] public section

/-!
# The per-location input trajectory of `hybridAutomaton/reach`, as CORA writes it

`aux_set_HA_inputs` in `postProcessing.m` (l. 617) reads, for a numeric `params.u`,
`uloc{i} = repmat({params.u},numLoc,1);` where `uloc = repmat(...)` was meant. `i` is the left-over
index of the loop over `params.U` (the last location, when `params.U` is a cell, as by default), and
the imaginary unit otherwise (an index error). The cell array `uloc` then has only entry `i` set, to
a cell of `numLoc` copies of `u`, and the rest empty. Entries are `Option (List α)`, `none` the
empty `[]`; locations are 0-based, so MATLAB's `i = numLoc` is `numLoc - 1`.
(`Theorems.UlocCoraCounterexample`).

# CORA's `uloc` gives locations the wrong input

With `numLoc ≥ 2` locations and the default cell `params.U`, a numeric `params.u` leaves location 0
with the empty input and gives the last location a cell of `numLoc` copies of `u` instead of `u`;
with one location it gives `{u}` instead of `u`. Read from `postProcessing.m` l. 617, not run
(`references/coverage/hybridDynamics/hybridAutomaton.md`, row `reach`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- `uloc` after `uloc{i} = repmat({u},numLoc,1)`, with 0-based left-over index `i`. -/
def HybridAutomaton.ulocCora {α : Type} (numLoc i : Nat) (u : α) (l : Nat) : Option (List α) :=
  if l = i then some (List.replicate numLoc u) else none


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.ulocCora_counterexample {α : Type} (numLoc : Nat) (hn : 2 ≤ numLoc)
    (u : α) : -- --- STMT ---
    HybridAutomaton.ulocCora numLoc (numLoc - 1) u 0 = none ∧
      HybridAutomaton.uloc numLoc u 0 = some u ∧
      HybridAutomaton.ulocCora numLoc (numLoc - 1) u (numLoc - 1) =
        some (List.replicate numLoc u) := by -- --- PROOF ---
  refine ⟨?_, ?_, ?_⟩
  · simp [HybridAutomaton.ulocCora]; omega
  · simp [HybridAutomaton.uloc]; omega
  · simp [HybridAutomaton.ulocCora]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
