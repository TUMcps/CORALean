module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# Reading a list of pairs whose values are all one

If every pair `(k,w)` of a list is replaced by `(k,v)`, reading a key of the list gives `v`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem lookup_map_const {α β : Type} (l : List (String × α)) (v : β) (p : String × α)
    (hp : p ∈ l) : (l.map fun q => (q.1, v)).lookup p.1 = some v := by -- --- PROOF ---
  induction l with
  | nil => simp at hp
  | cons q l ih =>
    rcases List.mem_cons.mp hp with rfl | h
    · simp
    · by_cases hq : p.1 = q.1
      · simp [hq]
      · have : (p.1 == q.1) = false := by simpa using hq
        simp [List.lookup_cons, this, ih h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
