module

public import CORALean.Specification.PointSegmentSignal.Theorems.AtAppendGe
public import CORALean.Specification.PointSegmentSignal.Theorems.AtAppendLt
public import CORALean.Specification.PointSegmentSignal.Theorems.AtBetween

@[expose] public section

/-!
# A signal after its last point at or before a time

Given a valid signal, an index `j` with the last point at or before `u` among its first `j`, and a
prefix `A` that is, after `u`, the interval value of `j`, the prefix followed by the points from `j`
on has the value of the signal at every time after `u`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T] [Zero T]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A prefix agreeing with the signal after `u`, followed by its tail, is the signal after `u`. -/
theorem PointSegmentSignal.suffix_at (s : PointSegmentSignal T) (hs : s.IsValid) (j : ℕ) (u : T)
    (hjle : ∀ x ∈ s.timePoints.take j, x ≤ u) (ha : ∃ a, s.timePoints[j - 1]? = some a ∧ a ≤ u)
    (hj1 : 1 ≤ j) (hj2 : j ≤ s.timePoints.length) (A : List T) (VA : List Bool)
    (hlen : VA.length = 2 * A.length) (hA : A ≠ []) (hAle : ∀ x ∈ A, x ≤ u) (after : Bool)
    (hafter : after = s.succIntervalValue j)
    (hAat : ∀ t, u < t → (PointSegmentSignal.mk A VA).at t = after) :
    ∀ t, u < t → (PointSegmentSignal.mk (A ++ s.timePoints.drop j)
      (VA ++ s.values.drop (2 * j))).at t = s.at t := by -- --- PROOF ---
  intro t ht
  obtain ⟨a, ha', hale⟩ := ha
  have hsl := hs.2.1
  -- the value of `s` just after its last point `≤ u`, up to the next point
  have hsafter : (∀ b, s.timePoints[j]? = some b → t < b) → s.at t = after := by
    intro hb
    have := s.at_between hs (j - 1) a t ha' (hale.trans_lt ht)
      (by rw [show j - 1 + 1 = j by omega]; exact hb)
    rw [this, hafter, show j - 1 + 1 = j by omega]
  -- `s` is the prefix of its first `j` points followed by the tail
  have e1 : s.timePoints.take j ++ s.timePoints.drop j = s.timePoints := List.take_append_drop _ _
  have e2 : s.values.take (2 * j) ++ s.values.drop (2 * j) = s.values := List.take_append_drop _ _
  have hVSlen : (s.values.take (2 * j)).length = 2 * (s.timePoints.take j).length := by
    simp [List.length_take]; omega
  have hsortS : (s.timePoints.drop j).Pairwise (· < ·) := hs.2.2.2.1.sublist (List.drop_sublist _ _)
  -- the tail is empty, or starts at a point `r`
  cases hS : s.timePoints.drop j with
  | nil =>
    have hjn : s.timePoints.length ≤ j := List.drop_eq_nil_iff.mp hS
    have hVS : s.values.drop (2 * j) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hVS, List.append_nil, List.append_nil, hAat t ht, hsafter]
    intro b hb
    rw [List.getElem?_eq_none (by omega)] at hb; simp at hb
  | cons r S' =>
    have hnr : s.timePoints[j]? = some r := by
      have h := congrArg (fun l => l[0]?) hS
      simpa [List.getElem?_drop] using h
    -- past `r` both signals are the tail; before it both stay on the same interval
    by_cases hr : r ≤ t
    · have e1' : s.timePoints.take j ++ r :: S' = s.timePoints := by rw [← hS]; exact e1
      rw [PointSegmentSignal.at_append_ge A r S' VA _ t hlen
        (fun x hx => (hAle x hx).trans ht.le) hr]
      have := PointSegmentSignal.at_append_ge (s.timePoints.take j) r S' (s.values.take (2 * j))
        (s.values.drop (2 * j)) t hVSlen (fun x hx => (hjle x hx).trans ht.le) hr
      rw [e1', e2] at this
      rw [this]
    · have hlt : ∀ r' ∈ r :: S', t < r' := by
        intro r' hr'
        rw [hS] at hsortS
        rcases List.mem_cons.mp hr' with rfl | hr''
        · exact not_le.mp hr
        · exact (not_le.mp hr).trans ((List.pairwise_cons.mp hsortS).1 r' hr'')
      rw [PointSegmentSignal.at_append_lt A (r :: S') VA _ hlen hA t hlt, hAat t ht, hsafter]
      intro b hb
      rw [hnr] at hb; cases hb; exact not_le.mp hr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
