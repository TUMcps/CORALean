module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# A valid prefix followed by the tail of a valid signal is valid

A valid signal followed by the points of another valid signal from index `j` on, with their values,
is valid when the points increase and the interval before point `j` agrees with the prefix's last.

## Inputs
* `s` – signal
* `j` – index of the first dropped-to point
* `tp'` – prefix time points
* `vs'` – prefix values

## Hypotheses
* `hs` – the signal is valid
* `hj1` – the index is positive
* `hj2` – the index is in range
* `hQ` – the prefix is a valid signal
* `hlt` – the prefix points are before the tail
* `hlast` – the prefix ends with the tail's preceding value

## Conclusion
* the prefix followed by the tail is valid
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T] [Zero T]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Reading a dropped list. -/
theorem aux_getD_drop (l : List Bool) (n i : ℕ) :
    (l.drop n).getD i false = l.getD (n + i) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A valid prefix followed by the tail from index `j` of a valid signal is valid. -/
theorem PointSegmentSignal.isValid_append_drop (s : PointSegmentSignal T) (hs : s.IsValid) (j : ℕ)
    (hj1 : 1 ≤ j) (hj2 : j ≤ s.timePoints.length) (tp' : List T) (vs' : List Bool)
    (hQ : (PointSegmentSignal.mk tp' vs').IsValid)
    (hlt : ∀ x ∈ tp', ∀ b, s.timePoints[j]? = some b → x < b)
    (hlast : vs'.getD (vs'.length - 1) false = s.values.getD (2 * j - 1) false) : -- --- CONCL ---
    (PointSegmentSignal.mk (tp' ++ s.timePoints.drop j) (vs' ++ s.values.drop (2 * j))).IsValid
      := by -- --- PROOF ---
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  obtain ⟨q1, q2, q3, q4, q5⟩ := hQ
  dsimp only at *
  refine ⟨by simp [q1], ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_drop]; omega
  · rw [List.head?_append, q3]; rfl
  -- the times increase across the junction
  · refine List.pairwise_append.mpr ⟨q4, h4.sublist (List.drop_sublist _ _), ?_⟩
    intro x hx y hy
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hy
    simp only [List.length_drop] at hm
    have hjn : j < s.timePoints.length := by omega
    have hb : s.timePoints[j]? = some s.timePoints[j] := List.getElem?_eq_getElem hjn
    have hx' := hlt x hx _ hb
    have hle : s.timePoints[j] ≤ s.timePoints[j + m] := by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp
      · exact (List.pairwise_iff_getElem.mp h4 j (j + m) hjn (by omega) (by omega)).le
    simp only [List.getElem_drop]
    exact hx'.trans_le hle
  -- no point is redundant: before the junction as in the prefix, after it as in `s`
  · intro k hk1 hk2
    simp only [List.length_append, List.length_drop] at hk2
    by_cases hka : k < tp'.length
    · have := q5 k hk1 hka
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega)]
      exact this
    -- a point from the tail; its neighbours are those it has in `s`
    · obtain ⟨m, rfl⟩ : ∃ m, k = tp'.length + m := ⟨k - tp'.length, by omega⟩
      have hsm := h5 (j + m) (by omega) (by omega)
      have e0 : (vs' ++ s.values.drop (2 * j)).getD (2 * (tp'.length + m)) false =
          s.values.getD (2 * (j + m)) false := by
        rw [List.getD_append_right _ _ _ _ (by omega), aux_getD_drop]
        congr 1; omega
      have e1 : (vs' ++ s.values.drop (2 * j)).getD (2 * (tp'.length + m) + 1) false =
          s.values.getD (2 * (j + m) + 1) false := by
        rw [List.getD_append_right _ _ _ _ (by omega), aux_getD_drop]
        congr 1; omega
      have e2 : (vs' ++ s.values.drop (2 * j)).getD (2 * (tp'.length + m) - 1) false =
          s.values.getD (2 * (j + m) - 1) false := by
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · rw [List.getD_append _ _ _ _ (by omega)]
          convert hlast using 2 <;> omega
        · rw [List.getD_append_right _ _ _ _ (by omega), aux_getD_drop]
          congr 1; omega
      rw [e0, e1, e2]
      exact hsm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
