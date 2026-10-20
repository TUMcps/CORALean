module

public import CORALean.Global.ReplaceKey

@[expose] public section

/-!
# Reading a list of pairs after replacing a key

`map(k) = v` changes the entry of key `k` and no other: reading `k` gives `v` if `k` was a key, and
any other key still gives what it did.

## Inputs
* `β` – value type
* `l` – list of pairs
* `k` – key replaced
* `v` – new value
* `k'` – key looked up

## Hypotheses
* none

## Conclusion
* the lookup returns the new value at the replaced key and the old one elsewhere
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem lookup_replaceKey {β : Type} (l : List (String × β)) (k : String) (v : β)
    (k' : String) : (replaceKey l k v).lookup k' =
      if k' = k then (if (l.lookup k).isSome then some v else none)
        else l.lookup k' := by -- --- PROOF ---
  induction l with
  | nil => simp [replaceKey]
  | cons a rest ih =>
    obtain ⟨a1, a2⟩ := a
    simp only [replaceKey] at ih ⊢
    by_cases h2 : k' = a1
    · subst h2
      by_cases h1 : k' = k
      · subst h1; simp
      · simp [h1]
    · have hb : (k' == a1) = false := by simpa using h2
      by_cases h1 : a1 = k
      · subst h1
        simp [List.lookup_cons, hb, ih, h2]
      · have hb2 : (k == a1) = false := by simpa using Ne.symm h1
        have hl : List.lookup k ((a1, a2) :: rest) = List.lookup k rest := by
          simp only [List.lookup_cons, hb2]
        rw [hl]
        simp [List.lookup_cons, hb, h1, ih]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
