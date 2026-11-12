module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# The prefix of a list through its first stop

`takeThrough p l` is `l` up to and including its first entry with `p` true, and all of `l` when
there is none. It is how CORA's reach stops at the first set that has left the invariant while
keeping that set. `getElem_takeThrough` reads an entry back when no earlier entry stops.

## Inputs
* `α` – element type
* `p` – stop test

## Output
* the prefix of a list through its first stop
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `l` up to and including its first entry with `p` true, all of `l` if there is none. -/
def takeThrough {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | a :: l => if p a then [a] else a :: takeThrough p l

/-- The prefix is no longer than the list. -/
theorem length_takeThrough_le {α : Type} (p : α → Bool) (l : List α) : -- --- CONCL ---
    (takeThrough p l).length ≤ l.length := by -- --- PROOF ---
  induction l with
  | nil => simp [takeThrough]
  | cons a l ih =>
    unfold takeThrough
    split_ifs
    · simp
    · simpa using ih

/-- An entry before which nothing stops is in the prefix, unchanged. -/
theorem getElem_takeThrough {α : Type} (p : α → Bool) (l : List α) (k : ℕ)
    (hk : k < l.length) (hp : ∀ j (hj : j < k), p l[j] = false) : -- --- CONCL ---
    ∃ h : k < (takeThrough p l).length, (takeThrough p l)[k] = l[k] := by -- --- PROOF ---
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    cases k with
    | zero =>
      unfold takeThrough
      split_ifs <;> simp
    | succ k =>
      have ha : p a = false := by simpa using hp 0 (Nat.succ_pos k)
      obtain ⟨h, he⟩ := ih k (by simpa using hk) fun j hj => by simpa using hp (j + 1) (by omega)
      simp only [takeThrough, ha, Bool.false_eq_true, if_false]
      exact ⟨by simpa using h, by simpa using he⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
