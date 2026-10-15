module

public import CORALean.Global.ReplaceKey

@[expose] public section

/-!
# Replacing a key keeps the keys

`map(k) = v` on a list of pairs changes a value and no key.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem map_fst_replaceKey {β : Type} (l : List (String × β)) (k : String) (v : β) :
    (replaceKey l k v).map Prod.fst = l.map Prod.fst := by -- --- PROOF ---
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [replaceKey, List.map_cons] at ih ⊢
    rw [ih]
    by_cases h : p.1 = k <;> simp [h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
