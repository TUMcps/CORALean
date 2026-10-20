module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# Replacing the entry of a key in a list of pairs

MATLAB's `containers.Map` keyed by strings is kept as a list of pairs in key order; `map(k) = v`
replaces the entry of key `k` and keeps the order. `replaceKey` does so for every pair with that
key.

## Inputs
* `β` – value type
* `l` – list of key-value pairs
* `k` – key replaced
* `v` – new value

## Output
* the list with the value of every pair of that key replaced
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `map(k) = v` on a list of pairs. -/
def replaceKey {β : Type} (l : List (String × β)) (k : String) (v : β) : List (String × β) :=
  l.map fun p => if p.1 = k then (k, v) else p

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
