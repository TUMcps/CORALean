module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# Reading a list of pairs after mapping its values

Mapping the second component of every pair of a list maps what a key reads: the lookup of `k` in
the mapped list is the old lookup, mapped.

## Inputs
* `β` – value type
* `γ` – mapped value type
* `g` – map of the values
* `l` – list of pairs
* `k` – key looked up

## Hypotheses
* none

## Conclusion
* the lookup in the mapped list is the mapped lookup
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem lookup_map_snd {β γ : Type} (g : β → γ) (l : List (String × β))
    (k : String) : -- --- CONCL ---
    (l.map fun p => (p.1, g p.2)).lookup k = (l.lookup k).map g := by -- --- PROOF ---
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.lookup]
    cases k == p.1
    · exact ih
    · rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
