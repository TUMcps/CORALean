module

public import CORALean.Specification.PointSegmentSignal.PointSegmentSignal
public import Mathlib.Order.Basic

@[expose] public section

/-!
# Counting the points below a time

In a strictly increasing list whose `m`-th entry `a ≤ t` and whose next entry exceeds `t`, exactly
the first `m + 1` entries are `≤ t`.

## Inputs
* `T` – element type
* `l` – list
* `t` – bound
* `a` – entry at the index
* `m` – index

## Hypotheses
* `hl` – the list strictly increases
* `hm` – the entry is at the index
* `h1` – the entry is at most the bound
* `h2` – the next entry exceeds the bound

## Conclusion
* exactly the first entries up to the index are at most the bound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem List.length_takeWhile_eq_of_pairwise_lt {T : Type} [LinearOrder T] (l : List T)
    (hl : l.Pairwise (· < ·)) (t a : T) (m : ℕ) (hm : l[m]? = some a) (h1 : a ≤ t)
    (h2 : ∀ b, l[m + 1]? = some b → t < b) :
    (l.takeWhile (· ≤ t)).length = m + 1 := by -- --- PROOF ---
  induction l generalizing m with
  | nil => simp at hm
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    cases m with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
      subst hm
      simp only [List.takeWhile_cons, h1, decide_true, if_true, List.length_cons]
      cases l with
      | nil => simp
      | cons b l' =>
        have := h2 b (by simp)
        simp [not_le.mpr this]
    | succ m =>
      -- the head is below the `m`-th entry, hence below `t`
      have hat : x ≤ t := by
        have hmem : a ∈ l := List.mem_of_getElem? (by simpa using hm)
        exact ((hl.1 a hmem).trans_le h1).le
      simp only [List.takeWhile_cons, hat, decide_true, if_true, List.length_cons]
      have := ih hl.2 m (by simpa using hm) (by intro b hb; exact h2 b (by simpa using hb))
      omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
