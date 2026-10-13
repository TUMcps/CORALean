module

@[expose] public section

/-!
# The per-location input of `hybridAutomaton/reach`, as intended

`uloc = repmat({params.u},numLoc,1)`: every location `l < numLoc` gets `u` itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Intended `uloc{l}`: `u` at every location below `numLoc`. -/
def HybridAutomaton.uloc {α : Type} (numLoc : Nat) (u : α) (l : Nat) : Option α :=
  if l < numLoc then some u else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
