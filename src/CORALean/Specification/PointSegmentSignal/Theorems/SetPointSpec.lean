module

public import CORALean.Specification.PointSegmentSignal.Operations.SetPoint
public import CORALean.Specification.PointSegmentSignal.Theorems.AtAppendLt
public import CORALean.Specification.PointSegmentSignal.Theorems.AtAppendGe
public import CORALean.Specification.PointSegmentSignal.Theorems.AtBetween
public import CORALean.Specification.PointSegmentSignal.Theorems.AtTimePoint
public import CORALean.Specification.PointSegmentSignal.Theorems.AtSnocLt
public import CORALean.Specification.PointSegmentSignal.Theorems.AtSnocEq
public import CORALean.Specification.PointSegmentSignal.Theorems.AtSnocGt
public import CORALean.Specification.PointSegmentSignal.Theorems.AtLast
public import CORALean.Specification.PointSegmentSignal.Theorems.IsValidTake
public import CORALean.Specification.PointSegmentSignal.Theorems.IsValidSnoc
public import CORALean.Specification.PointSegmentSignal.Theorems.IsValidAppendDrop
public import CORALean.Specification.PointSegmentSignal.Theorems.TakeWhileLePos
public import CORALean.Specification.PointSegmentSignal.Theorems.AtIdxFst
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.ListLtOfMemTake
public import CORALean.Specification.PointSegmentSignal.Theorems.ListLeOfMemTakeSucc
public import CORALean.Specification.PointSegmentSignal.Theorems.ListLeOfMemDrop
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.SuffixAt
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# Setting the value at one time

For a valid signal and a time `p ≥ 0`, `aux_setPoint` gives a valid signal whose value is `value` at
`p` and the signal's own value at every other time. A point is removed when it then matches both
intervals, set when it exists, inserted when `p` lies inside an interval.

## Inputs
* `s` – signal
* `p` – time to set
* `value` – value to set

## Hypotheses
* `hs` – the signal is valid
* `hp` – the time is nonnegative

## Conclusion
* a valid signal with the value at that time and unchanged elsewhere
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T] [Zero T]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Setting a single time to `value` changes the value there and nowhere else. -/
theorem PointSegmentSignal.setPoint_spec (s : PointSegmentSignal T) (hs : s.IsValid) (p : T)
    (hp : 0 ≤ p) (value : Bool) : -- --- CONCL ---
    (s.setPoint p value).IsValid ∧ ∀ t : T, 0 ≤ t → (s.setPoint p value).at t = if t = p then value
      else s.at t := by -- --- PROOF ---
  have hcur : (s.atIdx (p : WithTop T)).1 = s.at p := PointSegmentSignal.atIdx_fst s hs p hp
  have hi : (s.atIdx (p : WithTop T)).2 = (s.timePoints.takeWhile (· ≤ p)).length :=
    PointSegmentSignal.atIdx_snd s p
  obtain ⟨hi1, hi2, ⟨a, ha, hale⟩, hnext⟩ := PointSegmentSignal.takeWhile_le_pos s hs p hp
  unfold PointSegmentSignal.setPoint
  simp only []
  generalize hc : (s.atIdx (p : WithTop T)).1 = cur at *
  generalize hi' : (s.atIdx (p : WithTop T)).2 = i at *
  rw [← hi] at hi1 hi2 ha hnext
  have hgi : s.timePoints.getD (i - 1) 0 = a := by simp [List.getD_eq_getElem?_getD, ha]
  have hsort := hs.2.2.2.1
  have hlen := hs.2.1
  by_cases hcv : cur = value
  · -- already the value: nothing to do
    rw [if_pos hcv]
    refine ⟨hs, fun t ht => ?_⟩
    by_cases htp : t = p
    · rw [if_pos htp, htp, ← hcv, hcur]
    · rw [if_neg htp]
  · rw [if_neg hcv]
    by_cases hap : s.timePoints.getD (i - 1) 0 = p
    · -- `p` is a time point
      rw [if_pos (show TimeOrder.Eqv _ _ from hap)]
      have hap' : a = p := hgi.symm.trans hap
      subst hap'
      have hPle : ∀ x ∈ s.timePoints.take i, x ≤ a := fun x hx => by
        have hx' : x ∈ s.timePoints.take (i - 1 + 1) := by
          rw [show i - 1 + 1 = i by omega]; exact hx
        exact List.le_of_mem_take_succ s.timePoints hsort (i - 1) a ha x hx'
      have hgt : ∀ r ∈ s.timePoints.drop i, a < r := by
        intro r hr
        cases hb : s.timePoints[i]? with
        | none =>
          have : s.timePoints.length ≤ i := by
            by_contra hc; rw [List.getElem?_eq_getElem (by omega)] at hb; simp at hb
          rw [List.drop_eq_nil_of_le this] at hr; simp at hr
        | some b => exact (hnext b hb).trans_le (List.le_of_mem_drop s.timePoints hsort i b hb r hr)
      by_cases hrm : 1 < i ∧ s.precIntervalValue i = value ∧ s.succIntervalValue i = value
      · -- the point matches both intervals: remove it
        rw [if_pos hrm]
        have hP'lt : ∀ x ∈ s.timePoints.take (i - 1), x < a := fun x hx =>
          List.lt_of_mem_take s.timePoints hsort (i - 1) a ha x hx
        have hP'ne : s.timePoints.take (i - 1) ≠ [] := by
          intro h
          rcases List.take_eq_nil_iff.mp h with h | h
          · omega
          · exact hs.1 h
        have hVP'len : (s.values.take (2 * i - 2)).length =
            2 * (s.timePoints.take (i - 1)).length := by
          simp [List.length_take]; omega
        -- the value of the prefix just before the point is the removed point's
        have hVP'last : (s.values.take (2 * i - 2)).getD ((s.values.take (2 * i - 2)).length - 1)
            false = value := by
          have hl2 : (s.values.take (2 * i - 2)).length = 2 * i - 2 := by
            simp [List.length_take]; omega
          rw [hl2, List.getD_eq_getElem?_getD,
            List.getElem?_take_of_lt (show 2 * i - 2 - 1 < 2 * i - 2 by omega)]
          have := hrm.2.1
          simp only [PointSegmentSignal.precIntervalValue, List.getD_eq_getElem?_getD] at this
          rw [show 2 * i - 2 - 1 = 2 * i - 3 by omega]; exact this
        -- the prefix and the points after `p`, both valid, give a valid signal
        have hvalid : (PointSegmentSignal.mk (s.timePoints.take (i - 1) ++ s.timePoints.drop i)
            (s.values.take (2 * i - 2) ++ s.values.drop (2 * i))).IsValid := by
          have hP'v := PointSegmentSignal.isValid_take s hs (i - 1) (by omega) (by omega)
          rw [show 2 * (i - 1) = 2 * i - 2 by omega] at hP'v
          refine PointSegmentSignal.isValid_append_drop s hs i hi1 hi2 _ _ hP'v ?_ ?_
          · intro x hx b hb; exact (hP'lt x hx).trans (hnext b hb)
          · rw [hVP'last]
            have := hrm.2.2
            simp only [PointSegmentSignal.succIntervalValue] at this
            exact this.symm
        rw [List.eraseIdx_eq_take_drop_succ, show i - 1 + 1 = i by omega]
        -- before `p`, at `p` and after `p`
        refine ⟨hvalid, fun t ht => ?_⟩
        rcases lt_trichotomy t a with h | h | h
        · rw [PointSegmentSignal.at_append_lt _ _ _ _ hVP'len hP'ne t
            (fun r hr => h.trans (hgt r hr)), if_neg h.ne]
          have := PointSegmentSignal.at_append_lt (s.timePoints.take (i - 1))
            (s.timePoints.drop (i - 1))
            (s.values.take (2 * i - 2)) (s.values.drop (2 * i - 2)) hVP'len hP'ne t
            (fun r hr => h.trans_le (List.le_of_mem_drop s.timePoints hsort (i - 1) a ha r hr))
          rw [List.take_append_drop, List.take_append_drop] at this
          exact this.symm
        · subst h
          rw [PointSegmentSignal.at_append_lt _ _ _ _ hVP'len hP'ne t hgt,
            PointSegmentSignal.at_last _ _ hVP'len hP'ne t hP'lt, hVP'last, if_pos rfl]
        · rw [if_neg h.ne']
          refine PointSegmentSignal.suffix_at s hs i a hPle ⟨a, ha,
            le_rfl⟩ hi1 hi2 _ _ hVP'len hP'ne
            (fun x hx => (hP'lt x hx).le) (s.succIntervalValue i) rfl ?_ t h
          intro t' ht'
          rw [PointSegmentSignal.at_last _ _ hVP'len hP'ne t' (fun x hx => (hP'lt x hx).trans ht'),
            hVP'last, hrm.2.2]
      · -- set the point value
        rw [if_neg hrm]
        have hk : 2 * i - 2 < s.values.length := by omega
        -- only the value at index `2 * i - 2` changes
        have hget : ∀ n, n ≠ 2 * i - 2 →
            (s.values.set (2 * i - 2) value).getD n false = s.values.getD n false := by
          intro n hn
          simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
          rw [if_neg (Ne.symm hn)]
        have hset : (s.values.set (2 * i - 2) value).getD (2 * i - 2) false = value := by
          simp [List.getD_eq_getElem?_getD, hk]
        refine ⟨?_, fun t ht => ?_⟩
        -- the point `i - 1` is the only one whose neighbours changed
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hs
          refine ⟨h1, by simpa using h2, h3, h4, fun m hm1 hm2 => ?_⟩
          by_cases hmi : m = i - 1
          · subst hmi
            have h2i : 1 < i := by omega
            rw [show 2 * (i - 1) = 2 * i - 2 by omega, hset,
              hget (2 * i - 2 + 1) (by omega), hget (2 * i - 2 - 1) (by omega)]
            rintro ⟨e1, e2⟩
            apply hrm
            refine ⟨h2i, ?_, ?_⟩
            · simp only [PointSegmentSignal.precIntervalValue]
              rw [show 2 * i - 3 = 2 * i - 2 - 1 by omega]; exact e2.symm
            · simp only [PointSegmentSignal.succIntervalValue]
              rw [show 2 * i - 1 = 2 * i - 2 + 1 by omega]; exact e1.symm
          · have := h5 m hm1 hm2
            rw [hget (2 * m) (by omega), hget (2 * m + 1) (by omega), hget (2 * m - 1) (by omega)]
            exact this
        · simp only [TimeOrder.exists_mem_eqv_iff, PointSegmentSignal.at]
          by_cases hta : t = a
          · rw [hta, ← hi, if_pos ha, if_pos rfl, show 2 * (i - 1) = 2 * i - 2 by omega, hset]
          -- at another time the index read is not the changed one
          · rw [if_neg hta]
            generalize (s.timePoints.takeWhile (· ≤ t)).length - 1 = L
            by_cases hc : s.timePoints[L]? = some t
            · rw [if_pos hc, if_pos hc]
              apply hget
              intro h
              have hL : L = i - 1 := by omega
              rw [hL, ha] at hc
              exact hta (Option.some.inj hc).symm
            · rw [if_neg hc, if_neg hc]
              apply hget
              omega
    · -- `p` lies inside an interval: insert a new point
      rw [if_neg (show ¬ TimeOrder.Eqv _ _ from hap)]
      -- the last point `≤ p` is strictly before it
      have hlt : a < p := hale.lt_of_ne (fun h => hap (hgi.trans h))
      have hcs : cur = s.succIntervalValue i := by
        rw [hcur, s.at_between hs (i - 1) a p ha hlt
          (by rw [show i - 1 + 1 = i by omega]; exact hnext), show i - 1 + 1 = i by omega]
      have hPle : ∀ x ∈ s.timePoints.take i, x ≤ p := fun x hx => by
        have hx' : x ∈ s.timePoints.take (i - 1 + 1) := by
          rw [show i - 1 + 1 = i by omega]; exact hx
        exact (List.le_of_mem_take_succ s.timePoints hsort (i - 1) a ha x hx').trans hale
      have hPlt : ∀ x ∈ s.timePoints.take i, x < p := fun x hx => by
        have hx' : x ∈ s.timePoints.take (i - 1 + 1) := by
          rw [show i - 1 + 1 = i by omega]; exact hx
        exact (List.le_of_mem_take_succ s.timePoints hsort (i - 1) a ha x hx').trans_lt hlt
      -- the later points are above `p`
      have hgt : ∀ r ∈ s.timePoints.drop i, p < r := by
        intro r hr
        cases hb : s.timePoints[i]? with
        | none =>
          have : s.timePoints.length ≤ i := by
            by_contra hc; rw [List.getElem?_eq_getElem (by omega)] at hb; simp at hb
          rw [List.drop_eq_nil_of_le this] at hr; simp at hr
        | some b => exact (hnext b hb).trans_le (List.le_of_mem_drop s.timePoints hsort i b hb r hr)
      -- the prefix and its values have matching lengths
      have hVPlen : (s.values.take (2 * i)).length = 2 * (s.timePoints.take i).length := by
        simp [List.length_take]; omega
      have hPne : s.timePoints.take i ≠ [] := by
        intro h
        rcases List.take_eq_nil_iff.mp h with h | h
        · omega
        · exact hs.1 h
      -- the new point has value `value` and then the old interval value `cur`
      have hQ1 : (PointSegmentSignal.mk (s.timePoints.take i ++ [p])
          (s.values.take (2 * i) ++ [value, cur])).IsValid :=
        PointSegmentSignal.isValid_snoc _ _ p value cur
          (Or.inr ⟨PointSegmentSignal.isValid_take s hs i hi1 hi2, hPlt, fun h => hcv h.2.symm⟩)
      -- the result is the prefix with `p`, followed by the later points
      have e1 : s.timePoints.take i ++ p :: s.timePoints.drop i =
          (s.timePoints.take i ++ [p]) ++ s.timePoints.drop i := by simp
      have e2 : s.values.take (2 * i) ++ value :: cur :: s.values.drop (2 * i) =
          (s.values.take (2 * i) ++ [value, cur]) ++ s.values.drop (2 * i) := by simp
      simp only [e1, e2]
      have hlenQ1 : (s.values.take (2 * i) ++ [value, cur]).length =
          2 * (s.timePoints.take i ++ [p]).length := by simp [List.length_take]; omega
      have hQne : s.timePoints.take i ++ [p] ≠ [] := by simp
      -- validity and the value at every time
      refine ⟨?_, fun t ht => ?_⟩
      · refine PointSegmentSignal.isValid_append_drop s hs i hi1 hi2 _ _ hQ1 ?_ ?_
        · intro x hx b hb
          rcases List.mem_append.mp hx with hx | hx
          · exact (hPlt x hx).trans (hnext b hb)
          · simp at hx; exact hx ▸ hnext b hb
        · rw [List.getD_append_right _ _ _ _ (by simp [List.length_take])]
          simp [List.length_take, hcs, PointSegmentSignal.succIntervalValue,
            List.getD_eq_getElem?_getD]
      -- before `p`, at `p` and after `p`
      · rcases lt_trichotomy t p with h | h | h
        · rw [PointSegmentSignal.at_append_lt _ _ _ _ hlenQ1 hQne t
            (fun r hr => h.trans (hgt r hr)),
            PointSegmentSignal.at_snoc_lt _ _ p value cur hVPlen hPne t h, if_neg h.ne]
          have := PointSegmentSignal.at_append_lt (s.timePoints.take i) (s.timePoints.drop i)
            (s.values.take (2 * i)) (s.values.drop (2 * i)) hVPlen hPne t
            (fun r hr => h.trans (hgt r hr))
          rw [List.take_append_drop, List.take_append_drop] at this
          exact this.symm
        -- at `p` itself
        · subst h
          rw [PointSegmentSignal.at_append_lt _ _ _ _ hlenQ1 hQne t hgt,
            PointSegmentSignal.at_snoc_eq _ _ t value cur hVPlen hPlt, if_pos rfl]
        · rw [if_neg h.ne']
          refine PointSegmentSignal.suffix_at s hs i p hPle ⟨a, ha,
            hale⟩ hi1 hi2 _ _ hlenQ1 hQne ?_
            (s.succIntervalValue i) rfl ?_ t h
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hPle x hx
            · simp at hx; exact hx.le
          · intro t' ht'
            rw [PointSegmentSignal.at_snoc_gt _ _ p value cur hVPlen hPlt t' ht', hcs]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
