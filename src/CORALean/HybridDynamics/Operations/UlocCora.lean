/-!
# The per-location input trajectory of `hybridAutomaton/reach`, as CORA writes it

`aux_set_HA_inputs` in `postProcessing.m` (l. 617) reads, for a numeric `params.u`,
`uloc{i} = repmat({params.u},numLoc,1);` where `uloc = repmat(...)` was meant. `i` is the left-over
index of the loop over `params.U` (the last location, when `params.U` is a cell, as by default), and
the imaginary unit otherwise (an index error). The cell array `uloc` then has only entry `i` set, to
a cell of `numLoc` copies of `u`, and the rest empty. Entries are `Option (List α)`, `none` the
empty `[]`; locations are 0-based, so MATLAB's `i = numLoc` is `numLoc - 1`.
(`Theorems.UlocCoraCounterexample`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `uloc` after `uloc{i} = repmat({u},numLoc,1)`, with 0-based left-over index `i`. -/
def HybridAutomaton.ulocCora {α : Type} (numLoc i : Nat) (u : α) (l : Nat) : Option (List α) :=
  if l = i then some (List.replicate numLoc u) else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
