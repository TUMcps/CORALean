module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.At
public import Mathlib.Data.List.TakeWhile

@[expose] public section

/-!
# The last point at or before a time

In a valid signal and for a time `u ≥ 0`, the number `i` of time points `≤ u` is at least `1` and at
most the number of points, the `i`-th point is `≤ u` and the next one, if any, is `> u`.

## Inputs
* `s` – signal
* `u` – time

## Hypotheses
* `hs` – the signal is valid
* `h0` – the time is nonnegative

## Conclusion
* the count of points up to the time is the position of the last one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T] [Zero T]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The elements the prefix takes satisfy the predicate. -/
theorem aux_tw_get {α : Type} (p : α → Bool) (l : List α) (k : ℕ)
    (hk : k < (l.takeWhile p).length) :
    ∃ a, l[k]? = some a ∧ p a = true := by -- --- PROOF ---
  induction l generalizing k with
  | nil => simp at hk
  | cons x l ih =>
    by_cases hx : p x = true
    · simp only [List.takeWhile_cons, hx, if_true, List.length_cons] at hk
      cases k with
      | zero => exact ⟨x, rfl, hx⟩
      | succ k => obtain ⟨a, ha, hp⟩ := ih k (by omega); exact ⟨a, by simpa using ha, hp⟩
    · simp [hx] at hk

/-- The element after the prefix fails the predicate. -/
theorem aux_tw_next {α : Type} (p : α → Bool) (l : List α) (b : α)
    (hb : l[(l.takeWhile p).length]? = some b) :
    p b = false := by -- --- PROOF ---
  induction l with
  | nil => simp at hb
  | cons x l ih =>
    by_cases hx : p x = true
    · simp only [List.takeWhile_cons, hx, if_true, List.length_cons] at hb
      exact ih (by simpa using hb)
    · simp only [List.takeWhile_cons, hx] at hb
      simp at hb; subst hb; simpa using hx


-- =======================================  MAIN THEOREM  ======================================= --

/-- The count of points `≤ u` is the position of the last one. -/
theorem PointSegmentSignal.takeWhile_le_pos (s : PointSegmentSignal T) (hs : s.IsValid) (u : T)
    (h0 : 0 ≤ u) : -- --- CONCL ---
    1 ≤ (s.timePoints.takeWhile (· ≤ u)).length ∧ (s.timePoints.takeWhile (· ≤ u)).length ≤
      s.timePoints.length ∧
      (∃ a, s.timePoints[(s.timePoints.takeWhile (· ≤ u)).length - 1]? = some a ∧ a ≤ u) ∧
      (∀ b, s.timePoints[(s.timePoints.takeWhile (· ≤ u)).length]? = some b → u < b)
      := by -- --- PROOF ---
  have hL : (s.timePoints.takeWhile (· ≤ u)).length ≤ s.timePoints.length :=
    (List.takeWhile_sublist _).length_le
  have h1 : 1 ≤ (s.timePoints.takeWhile (· ≤ u)).length := by
    obtain ⟨-, -, h3, -, -⟩ := hs
    obtain ⟨l, hl⟩ : ∃ l, s.timePoints = 0 :: l := by
      cases h : s.timePoints with
      | nil => simp [h] at h3
      | cons a l => simp [h] at h3; exact ⟨l, by rw [h3]⟩
    rw [hl]; simp [h0]
  refine ⟨h1, hL, ?_, ?_⟩
  · obtain ⟨a, ha, hp⟩ :=
      aux_tw_get (fun x : T => decide (x ≤ u)) s.timePoints
        ((s.timePoints.takeWhile (· ≤ u)).length - 1) (by omega)
    exact ⟨a, ha, by simpa using hp⟩
  · intro b hb
    have := aux_tw_next _ s.timePoints b hb
    simpa using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
