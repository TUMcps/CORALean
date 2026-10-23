module

public import CORALean.Global.ReplaceKey

@[expose] public section

/-!
# Replacing a key, then mapping the values

Mapping the second component of every pair commutes with `map(k) = v`: replacing and then mapping
is replacing by the mapped value in the mapped list.

## Inputs
* `β` – value type
* `γ` – mapped value type
* `g` – map of the values
* `l` – list of pairs
* `k` – key replaced
* `v` – new value

## Hypotheses
* none

## Conclusion
* mapping after the replacement is the replacement in the mapped list
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem replaceKey_map_snd {β γ : Type} (g : β → γ) (l : List (String × β)) (k : String)
    (v : β) : -- --- CONCL ---
    (replaceKey l k v).map (fun p => (p.1, g p.2)) =
      replaceKey (l.map fun p => (p.1, g p.2)) k (g v) := by -- --- PROOF ---
  unfold replaceKey
  simp only [List.map_map]
  congr 1
  funext p
  by_cases h : p.1 = k <;> simp [h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
