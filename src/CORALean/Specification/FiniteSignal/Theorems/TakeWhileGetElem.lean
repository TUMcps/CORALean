module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.Basic

@[expose] public section

/-!
# The entries a prefix takes

The entries `takeWhile` takes satisfy the predicate, and the next one does not.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The entries the prefix takes satisfy the predicate, the next one does not. -/
theorem List.takeWhile_getElem {α : Type} (p : α → Bool) : -- --- STMT ---
    ∀ (l : List α), (∀ (m : ℕ) (hm : m < (l.takeWhile p).length),
        p (l[m]'(Nat.lt_of_lt_of_le hm (List.takeWhile_sublist p).length_le)) = true) ∧
      ∀ (hk : (l.takeWhile p).length < l.length), p (l[(l.takeWhile p).length]) = false
  | [] => by simp
  | x :: l => by
    obtain ⟨i1, i2⟩ := List.takeWhile_getElem p l
    by_cases hx : p x = true
    · simp only [List.takeWhile_cons, hx, if_true, List.length_cons]
      refine ⟨fun m hm => ?_, fun hk => ?_⟩
      · cases m with
        | zero => simpa using hx
        | succ m => exact i1 m (by simpa using hm)
      · exact i2 (by simpa using hk)
    -- rewrite and simplify
    · simp only [List.takeWhile_cons, hx]
      simpa using hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
