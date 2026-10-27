module

public import CORALean.Specification.PointSegmentSignal.Operations.Set
public import CORALean.Specification.STLInterval.Theorems.NotMemBoundsOfEmptyBounds
public import CORALean.Specification.STLInterval.Definitions.IsInBounds
public import CORALean.Specification.PointSegmentSignal.Theorems.SetPointSpec
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
public import CORALean.Specification.PointSegmentSignal.Theorems.SuffixAt
public import Mathlib.Data.List.GetD
public import CORALean.Specification.STLInterval.Theorems.SetIffMemBounds
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# Setting a time interval sets exactly that interval

`set(obj,interval,value)` of a valid signal and an `stlInterval` whose lower bound is `≥ 0` is valid
and has `value` at the times the interval denotes, the signal's own value elsewhere: the interval's
real bounds are those of `aux_setBounds_spec`.

## Inputs
* `s` – signal
* `I` – time interval
* `value` – value to set

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* a valid signal with the value on the interval and unchanged elsewhere
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {T : Type} [LinearOrder T] [Zero T]

/-- `step_isNewPointOk` as a proposition. -/
private theorem PointSegmentSignal.aux_isNewPointOk_iff (s : PointSegmentSignal T) (i : ℕ) (p : T)
    (vals : List Bool) : -- --- CONCL ---
    s.step_isNewPointOk i p vals = true ↔ (s.timePoints.getD (i - 1) 0 = p ∧
      (p = 0 ∨ vals.getD 0 false ≠
      vals.getD 1 false ∨ vals.getD 0 false ≠ s.precIntervalValue i)) ∨
      (s.timePoints.getD (i - 1) 0 ≠ p ∧ ∃ v ∈ vals, v ≠ s.succIntervalValue i)
      := by -- --- PROOF ---
  unfold PointSegmentSignal.step_isNewPointOk
  by_cases h : s.timePoints.getD (i - 1) 0 = p
  · simp only [TimeOrder.eqv_iff_eq, h, if_true, decide_eq_true_eq, true_and, ne_eq,
      not_true_eq_false, false_and, or_false]
  · simp only [TimeOrder.eqv_iff_eq, h, if_false, List.any_eq_true, decide_eq_true_eq, ne_eq,
      not_false_eq_true, true_and, false_and, false_or]


/-- The lower prefix of `set`: the points before `lb` and the new point at `lb`, if any. -/
private def aux_lowerPrefix (s : PointSegmentSignal T) (lb : T) (lc value : Bool) :
    PointSegmentSignal T :=
  let before := (s.atIdx (lb : WithTop T)).1
  let i := (s.atIdx (lb : WithTop T)).2
  let lVal := if lc then [value, value] else [before, value]
  let addL := s.step_isNewPointOk i lb lVal
  let i' := if s.timePoints.getD (i - 1) 0 = lb then i - 1 else i
  ⟨s.timePoints.take i' ++ (if addL then [lb] else []),
    s.values.take (2 * i') ++ (if addL then lVal else [])⟩


/-- The index of the first point `set` drops or replaces at the lower end. -/
private def aux_lowerIdx (s : PointSegmentSignal T) (lb : T) : ℕ :=
  if s.timePoints.getD ((s.atIdx (lb : WithTop T)).2 - 1) 0 = lb then
    (s.atIdx (lb : WithTop T)).2 - 1
  else (s.atIdx (lb : WithTop T)).2


/-- Facts about the lower end: the points before it, the new point and its neighbours. -/
private theorem aux_ls_key (s : PointSegmentSignal T) (hs : s.IsValid) (lb : T) (h0 : 0 ≤ lb)
    (lc value : Bool) (before : Bool) (i : ℕ) (lVal : List Bool) (addL : Bool) (i' : ℕ)
    (P : List T) (VP : List Bool) (hb : before = (s.atIdx (lb : WithTop T)).1)
    (hi : i = (s.atIdx (lb : WithTop T)).2)
    (hl : lVal = if lc then [value, value] else [before, value])
    (ha : addL = s.step_isNewPointOk i lb lVal)
    (hi' : i' = if s.timePoints.getD (i - 1) 0 = lb then i - 1 else i)
    (hP : P = s.timePoints.take i') (hVP : VP = s.values.take (2 * i')) : -- --- CONCL ---
    (∀ x ∈ P, x < lb) ∧ VP.length = 2 * P.length ∧ (∀ r ∈ s.timePoints.drop i', lb ≤ r) ∧ before =
      s.at lb ∧ (P = [] → lb = 0 ∧ addL = true) ∧ (addL = false → P ≠ [] ∧ VP.getD (VP.length - 1)
      false = value ∧ lVal.getD 0 false = value) ∧ (addL = true → P ≠ [] → ¬ (lVal.getD 0 false =
      lVal.getD 1 false ∧ lVal.getD 0 false = VP.getD (VP.length - 1) false)) := by -- --- PROOF ---
  obtain ⟨hi1, hi2, ⟨a, ha', hale⟩, hnext⟩ := PointSegmentSignal.takeWhile_le_pos s hs lb h0
  have hi0 : i = (s.timePoints.takeWhile (· ≤ lb)).length := by
    rw [hi]; exact PointSegmentSignal.atIdx_snd s lb
  have hbefore : before = s.at lb := by rw [hb]; exact PointSegmentSignal.atIdx_fst s hs lb h0
  have hl1 : lVal.getD 1 false = value := by rw [hl]; cases lc <;> simp
  have hmem : ∀ v ∈ lVal, v = lVal.getD 0 false ∨ v = lVal.getD 1 false := by
    intro v hv; rw [hl] at hv ⊢; cases lc <;> simp at hv ⊢ <;> exact hv
  have hsort := hs.2.2.2.1
  have hlen := hs.2.1
  rw [← hi0] at hi1 hi2 ha' hnext
  have hnp := PointSegmentSignal.aux_isNewPointOk_iff s i lb lVal
  rw [← ha] at hnp
  have hgi : s.timePoints.getD (i - 1) 0 = a := by simp [List.getD_eq_getElem?_getD, ha']
  rcases hale.lt_or_eq with hlt | heq
  · -- the last point at or before `lb` is strictly before it
    have hi'' : i' = i := by rw [hi', hgi, if_neg hlt.ne]
    have hPx : ∀ x ∈ P, x < lb := fun x hx => by
      have hx' : x ∈ s.timePoints.take (i - 1 + 1) := by
        rw [show i - 1 + 1 = i by omega, ← hi'', ← hP]; exact hx
      exact (List.le_of_mem_take_succ s.timePoints hsort (i - 1) a ha' x hx').trans_lt hlt
    have hPlen : P.length = i := by rw [hP, hi'']; simp [List.length_take]; omega
    have hVPlen : VP.length = 2 * P.length := by
      rw [hVP, hPlen, hi'']; simp [List.length_take]; omega
    have hdrop : ∀ r ∈ s.timePoints.drop i', lb ≤ r := by
      intro r hr
      rw [hi''] at hr
      cases hb' : s.timePoints[i]? with
      | none =>
        have : s.timePoints.length ≤ i := by
          by_contra hc; rw [List.getElem?_eq_getElem (by omega)] at hb'; simp at hb'
        rw [List.drop_eq_nil_of_le this] at hr; simp at hr
      | some b => exact (hnext b hb').le.trans (List.le_of_mem_drop s.timePoints hsort i b hb' r hr)
    -- the last value kept is the interval value of the last point kept
    have hVPlast : VP.getD (VP.length - 1) false = s.succIntervalValue i := by
      have hl2 : VP.length = 2 * i := by rw [hVPlen, hPlen]
      rw [hl2, hVP, hi'', PointSegmentSignal.succIntervalValue, List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
    -- the claims: the prefix is never empty here, and what no new point means
    refine ⟨hPx, hVPlen, hdrop, hbefore, ?_, ?_, ?_⟩
    · intro hP0; rw [hP0] at hPlen; simp at hPlen; omega
    · intro hf
      have hnot : ¬ (addL = true) := by rw [Bool.not_eq_true]; exact hf
      rw [hnp] at hnot
      have hall : ∀ v ∈ lVal, v = s.succIntervalValue i := by
        intro v hv; by_contra hv'
        exact hnot (Or.inr ⟨by rw [hgi]; exact hlt.ne, v, hv, hv'⟩)
      have e0 := hall (lVal.getD 0 false) (by rw [hl]; cases lc <;> simp)
      have e1 := hall (lVal.getD 1 false) (by rw [hl]; cases lc <;> simp)
      refine ⟨fun hP0 => ?_, hVPlast.trans (e1.symm.trans hl1), e0.trans (e1.symm.trans hl1)⟩
      rw [hP0] at hPlen; simp at hPlen; omega
    -- a new point is not redundant with the prefix's last value
    · intro ht hP0
      rw [hVPlast]
      rintro ⟨e0, e1⟩
      rw [hnp] at ht
      rcases ht with ⟨hh, -⟩ | ⟨-, v, hv, hv'⟩
      · rw [hgi] at hh; exact hlt.ne hh
      · rcases hmem v hv with rfl | rfl
        · exact hv' e1
        · exact hv' (e0.symm.trans e1)
  · -- the last point at or before `lb` is `lb` itself, and it is replaced
    subst heq
    have hi'' : i' = i - 1 := by rw [hi', if_pos hgi]
    have hPx : ∀ x ∈ P, x < a := fun x hx => by
      rw [hP, hi''] at hx
      exact List.lt_of_mem_take s.timePoints hsort (i - 1) a ha' x hx
    have hPlen : P.length = i - 1 := by rw [hP, hi'']; simp [List.length_take]; omega
    have hVPlen : VP.length = 2 * P.length := by
      rw [hVP, hPlen, hi'']; simp [List.length_take]; omega
    have hdrop : ∀ r ∈ s.timePoints.drop i', a ≤ r := by
      intro r hr
      rw [hi''] at hr
      exact List.le_of_mem_drop s.timePoints hsort (i - 1) a ha' r hr
    -- an empty prefix means `lb` is the first point `0`
    have hzero : P = [] → a = 0 := by
      intro hP0
      rw [hP0] at hPlen; simp at hPlen
      have hi1' : i = 1 := by omega
      have := hs.2.2.1
      subst hi1'
      obtain ⟨l, hl'⟩ : ∃ l, s.timePoints = 0 :: l := by
        cases h : s.timePoints with
        | nil => simp [h] at this
        | cons c l => simp [h] at this; exact ⟨l, by rw [this]⟩
      rw [hl'] at ha'; simp at ha'; exact ha'.symm
    -- a non-empty prefix means `lb` is a later point than `0`
    have hpos : P ≠ [] → a ≠ 0 := by
      intro hP0
      have hi2' : 2 ≤ i := by
        by_contra hc
        apply hP0; apply List.eq_nil_of_length_eq_zero; omega
      have h00 : s.timePoints[0]? = some 0 := by
        have := hs.2.2.1
        rwa [List.head?_eq_getElem?] at this
      have := List.pairwise_iff_getElem.mp hsort 0 (i - 1) (by omega) (by omega) (by omega)
      obtain ⟨_, e1⟩ := List.getElem?_eq_some_iff.mp ha'
      obtain ⟨_, e0⟩ := List.getElem?_eq_some_iff.mp h00
      rw [e0, e1] at this
      exact this.ne'
    -- the last value kept is the interval value before the replaced point
    have hVPlast : P ≠ [] → VP.getD (VP.length - 1) false = s.precIntervalValue i := by
      intro hP0
      have hi2' : 2 ≤ i := by
        by_contra hc
        apply hP0; apply List.eq_nil_of_length_eq_zero; omega
      have hl2 : VP.length = 2 * (i - 1) := by rw [hVPlen, hPlen]
      rw [hl2, hVP, hi'', PointSegmentSignal.precIntervalValue, List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt (show 2 * (i - 1) - 1 < 2 * (i - 1) by omega)]
      rw [show 2 * (i - 1) - 1 = 2 * i - 3 by omega]
    -- the claims: an empty prefix forces a new point; what no new point means
    refine ⟨hPx, hVPlen, hdrop, hbefore, ?_, ?_, ?_⟩
    · intro hP0
      refine ⟨hzero hP0, ?_⟩
      have : addL = true := hnp.mpr (Or.inl ⟨hgi, Or.inl (hzero hP0)⟩)
      exact this
    · intro hf
      have hnot : ¬ (addL = true) := by rw [Bool.not_eq_true]; exact hf
      rw [hnp] at hnot
      have hnn : ¬ (a = 0 ∨ lVal.getD 0 false ≠ lVal.getD 1 false ∨
          lVal.getD 0 false ≠ s.precIntervalValue i) := fun h => hnot (Or.inl ⟨hgi, h⟩)
      simp only [not_or, not_not] at hnn
      -- so the prefix is non-empty and its last value is the new point's
      have hP0 : P ≠ [] := fun h => hnn.1 (hzero h)
      refine ⟨hP0, ?_, ?_⟩
      · rw [hVPlast hP0, ← hnn.2.2, hnn.2.1, hl1]
      · rw [hnn.2.1, hl1]
    · intro ht hP0
      rw [hnp] at ht
      rw [hVPlast hP0]
      rcases ht with ⟨-, h1 | h1 | h1⟩ | ⟨hh, -⟩
      · exact absurd h1 (hpos hP0)
      · exact fun h => h1 h.1
      · exact fun h => h1 h.2
      · exact absurd hgi hh


/-- The lower prefix is valid and has the right values before, at and after `lb`. -/
private theorem aux_ls_spec (s : PointSegmentSignal T) (hs : s.IsValid) (lb : T) (h0 : 0 ≤ lb)
    (lc value : Bool) : -- --- CONCL ---
    (aux_lowerPrefix s lb lc value).IsValid ∧
      (∀ x ∈ (aux_lowerPrefix s lb lc value).timePoints, x ≤ lb) ∧
      (∀ r ∈ s.timePoints.drop (aux_lowerIdx s lb), lb ≤ r) ∧
      (∀ t : T, 0 ≤ t → t < lb → (aux_lowerPrefix s lb lc value).at t = s.at t) ∧
      (aux_lowerPrefix s lb lc value).at lb = (if lc then value else s.at lb) ∧
      (∀ t : T, lb < t → (aux_lowerPrefix s lb lc value).at t = value) ∧
      (aux_lowerPrefix s lb lc value).values.getD
      ((aux_lowerPrefix s lb lc value).values.length - 1) false = value := by -- --- PROOF ---
  unfold aux_lowerPrefix aux_lowerIdx
  simp only []
  generalize hb : (s.atIdx (lb : WithTop T)).1 = before
  generalize hi : (s.atIdx (lb : WithTop T)).2 = i
  generalize hl : (if lc = true then [value, value] else [before, value]) = lVal
  generalize ha : s.step_isNewPointOk i lb lVal = addL
  generalize hi' : (if s.timePoints.getD (i - 1) 0 = lb then i - 1 else i) = i'
  have key := aux_ls_key s hs lb h0 lc value before i lVal addL i' (s.timePoints.take i')
    (s.values.take (2 * i')) hb.symm hi.symm hl.symm ha.symm hi'.symm rfl rfl
  obtain ⟨hPx, hVPlen, hdrop, hbef, hP0, hnoadd, hadd⟩ := key
  have hlVal : lVal = [lVal.getD 0 false, lVal.getD 1 false] := by
    rw [← hl]; cases lc <;> simp
  have hl1 : lVal.getD 1 false = value := by rw [← hl]; cases lc <;> simp
  have hn : s.timePoints.length * 2 = s.values.length := by have := hs.2.1; omega
  have hi_le : i ≤ s.timePoints.length := by
    rw [← hi, PointSegmentSignal.atIdx_snd]; exact (List.takeWhile_sublist _).length_le
  have hi'_le : i' ≤ i := by rw [← hi']; split_ifs <;> omega
  -- name the prefix and its values
  generalize hP : List.take i' s.timePoints = P at *
  generalize hVP : List.take (2 * i') s.values = VP at *
  have hsat : ∀ t : T, 0 ≤ t → t < lb → (PointSegmentSignal.mk P VP).at t = s.at t := by
    intro t ht0 htl
    have hPne : P ≠ [] := fun h => by
      have := (hP0 h).1; rw [this] at htl; exact absurd htl (not_lt.mpr ht0)
    have := PointSegmentSignal.at_append_lt P (s.timePoints.drop i') VP (s.values.drop (2 * i'))
      hVPlen hPne t (fun r hr => htl.trans_le (hdrop r hr))
    have e1 : P ++ s.timePoints.drop i' = s.timePoints := by rw [← hP, List.take_append_drop]
    have e2 : VP ++ s.values.drop (2 * i') = s.values := by rw [← hVP, List.take_append_drop]
    rw [e1, e2] at this
    exact this.symm
  have hvalid_take : P ≠ [] → (PointSegmentSignal.mk P VP).IsValid := by
    intro hPne
    have hi'1 : 1 ≤ i' := by
      by_contra hc; apply hPne; rw [← hP]; simp; omega
    rw [← hP, ← hVP]
    exact PointSegmentSignal.isValid_take s hs i' hi'1 (by omega)
  -- with or without a new point at `lb`
  cases addL
  · -- no new point at `lb`
    obtain ⟨hPne, hwP, hl0⟩ := hnoadd rfl
    simp only [Bool.false_eq_true, if_false, List.append_nil]
    refine ⟨hvalid_take hPne, fun x hx => (hPx x hx).le, hdrop, hsat, ?_, ?_, hwP⟩
    · rw [PointSegmentSignal.at_last P VP hVPlen hPne lb hPx, hwP]
      cases lc
      · rw [← hbef, ← hl0, ← hl]; simp
      · rfl
    · intro t ht
      rw [PointSegmentSignal.at_last P VP hVPlen hPne t (fun x hx => (hPx x hx).trans ht), hwP]
  · -- a new point at `lb`
    simp only [if_true]
    rw [hlVal]
    set pv := lVal.getD 0 false with hpv
    set iv := lVal.getD 1 false with hiv
    refine ⟨?_, ?_, hdrop, ?_, ?_, ?_, ?_⟩
    · by_cases hPe : P = []
      · obtain ⟨hlb0, -⟩ := hP0 hPe
        have hVPe : VP = [] := by
          rw [hPe] at hVPlen; exact List.eq_nil_of_length_eq_zero (by simpa using hVPlen)
        rw [hPe, hVPe]
        exact PointSegmentSignal.isValid_snoc [] [] lb pv iv (Or.inl ⟨rfl, rfl, hlb0⟩)
      -- append the new point to the valid prefix
      · refine PointSegmentSignal.isValid_snoc P VP lb pv iv (Or.inr ⟨hvalid_take hPe, hPx, ?_⟩)
        have := hadd rfl hPe
        exact fun h => this ⟨h.2, h.1⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (hPx x hx).le
      · simp at hx; exact hx.le
    · intro t ht0 htl
      have hPne : P ≠ [] := fun h => by
        have := (hP0 h).1; rw [this] at htl; exact absurd htl (not_lt.mpr ht0)
      rw [PointSegmentSignal.at_snoc_lt P VP lb pv iv hVPlen hPne t htl, hsat t ht0 htl]
    · rw [PointSegmentSignal.at_snoc_eq P VP lb pv iv hVPlen hPx]
      cases lc
      · rw [hpv, ← hl]; simpa using hbef
      · rw [hpv, ← hl]; simp
    · intro t ht
      rw [PointSegmentSignal.at_snoc_gt P VP lb pv iv hVPlen hPx t ht, hl1]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simpa using hl1


/-- Facts about the points at or before the upper end. -/
private theorem aux_us_facts (s : PointSegmentSignal T) (hs : s.IsValid) (lb u : T) (hlb : 0 ≤ lb)
    (hlu : lb < u) (j : ℕ) (hj : j = (s.atIdx (u : WithTop T)).2) : -- --- CONCL ---
    1 ≤ j ∧ j ≤ s.timePoints.length ∧ (∀ x ∈ s.timePoints.take j, x ≤ u) ∧
      (∀ b, s.timePoints[j]? = some b → u < b) ∧ (∀ r ∈ s.timePoints.drop j, u < r) ∧
      (∃ a, s.timePoints[j - 1]? = some a ∧ a ≤ u) := by -- --- PROOF ---
  have hu0 : 0 ≤ u := hlb.trans hlu.le
  obtain ⟨hj1, hj2, ⟨a, ha, hale⟩, hnext⟩ := PointSegmentSignal.takeWhile_le_pos s hs u hu0
  have hj' : j = (s.timePoints.takeWhile (· ≤ u)).length := by
    rw [hj]; exact PointSegmentSignal.atIdx_snd s u
  rw [← hj'] at hj1 hj2 ha hnext
  refine ⟨hj1, hj2, ?_, hnext, ?_, ⟨a, ha, hale⟩⟩
  · intro x hx
    have hx' : x ∈ s.timePoints.take (j - 1 + 1) := by rw [show j - 1 + 1 = j by omega]; exact hx
    exact List.le_of_mem_take_succ s.timePoints hs.2.2.2.1 (j - 1) a ha x hx' |>.trans hale
  · intro r hr
    cases hb : s.timePoints[j]? with
    | none =>
      have : s.timePoints.length ≤ j := by
        by_contra hc; rw [List.getElem?_eq_getElem (by omega)] at hb; simp at hb
      rw [List.drop_eq_nil_of_le this] at hr; simp at hr
    | some b =>
      exact (hnext b hb).trans_le (List.le_of_mem_drop s.timePoints hs.2.2.2.1 j b hb r hr)


/-- The part from the lower prefix on is valid and has the right values around `ub`. -/
private theorem aux_us_spec (s : PointSegmentSignal T) (hs : s.IsValid) (Q : PointSegmentSignal T)
    (lb u : T) (hlb : 0 ≤ lb) (hlu : lb < u) (rc value : Bool) (hQv : Q.IsValid)
    (hQle : ∀ x ∈ Q.timePoints, x ≤ lb) (hQabove : ∀ t, lb < t → Q.at t = value)
    (hQlast : Q.values.getD (Q.values.length - 1) false = value) (j : ℕ) (afterPoint after : Bool)
    (rVal : List Bool) (addR : Prop) [Decidable addR] (hj : j = (s.atIdx (u : WithTop T)).2)
    (hap : afterPoint = (s.atIdx (u : WithTop T)).1) (haf : after = s.succIntervalValue j)
    (hr : rVal = if rc then [value, after] else [afterPoint, after])
    (haddR : addR ↔ rVal.any (fun v => v ≠ value) = true) (R : PointSegmentSignal T) (hR : R =
    ⟨Q.timePoints ++ (if addR then [u] else []) ++ s.timePoints.drop j, Q.values ++
    (if addR then rVal else []) ++ s.values.drop (2 * j)⟩) : -- --- CONCL ---
    R.IsValid ∧ (∀ t, 0 ≤ t → t < u → R.at t = Q.at t) ∧ R.at u = (if rc then value else s.at u) ∧ ∀
      t, u < t → R.at t = s.at t := by -- --- PROOF ---
  subst hR
  have hu0 : 0 ≤ u := hlb.trans hlu.le
  obtain ⟨hj1, hj2, hjle, hnext, hgt, ha⟩ := aux_us_facts s hs lb u hlb hlu j hj
  have hapt : afterPoint = s.at u := by rw [hap]; exact PointSegmentSignal.atIdx_fst s hs u hu0
  have hQlen := hQv.2.1
  have hQne := hQv.1
  obtain ⟨r0, r1, rfl⟩ : ∃ r0 r1, rVal = [r0, r1] := by rw [hr]; cases rc <;> simp
  have hr0 : r0 = (if rc then value else s.at u) := by
    cases rc
    · simp only [Bool.false_eq_true, if_false] at hr ⊢; rw [← hapt]; exact (List.cons.inj hr).1
    · simp only [if_true] at hr ⊢; exact (List.cons.inj hr).1
  have hr1 : r1 = after := by
    cases rc
    · simp only [Bool.false_eq_true, if_false] at hr; exact (List.cons.inj (List.cons.inj hr).2).1
    · simp only [if_true] at hr; exact (List.cons.inj (List.cons.inj hr).2).1
  have hQu : ∀ x ∈ Q.timePoints, x < u := fun x hx => (hQle x hx).trans_lt hlu
  have hVSlast : after = s.values.getD (2 * j - 1) false := by rw [haf]; rfl
  have hsortS := hs.2.2.2.1
  by_cases hA : addR
  · -- a new point at the upper end
    simp only [hA, if_true]
    have haddr : r0 ≠ value ∨ r1 ≠ value := by
      have := haddR.mp hA; simpa using this
    have hnr : ¬ (r0 = Q.values.getD (Q.values.length - 1) false ∧ r0 = r1) := by
      rw [hQlast]; rintro ⟨e0, e1⟩; rcases haddr with h | h
      · exact h e0
      · exact h (e1 ▸ e0)
    have hQR := PointSegmentSignal.isValid_snoc Q.timePoints Q.values u r0 r1 (Or.inr ⟨hQv, hQu,
      hnr⟩)
    have hlenQR : (Q.values ++ [r0, r1]).length = 2 * (Q.timePoints ++ [u]).length := by
      simp [hQlen]; omega
    -- the prefix with the new upper point is non-empty and below `u`
    have hAne : Q.timePoints ++ [u] ≠ [] := by simp
    have hAle : ∀ x ∈ Q.timePoints ++ [u], x ≤ u := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (hQu x hx).le
      · simp at hx; exact hx.le
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine PointSegmentSignal.isValid_append_drop s hs j hj1 hj2 _ _ hQR ?_ ?_
      · intro x hx b hb
        exact (hAle x hx).trans_lt (hnext b hb)
      · rw [List.getD_append_right _ _ _ _ (by simp [hQlen])]
        simpa [hQlen, hr1, List.getD_eq_getElem?_getD] using hVSlast
    · intro t ht0 htu
      rw [PointSegmentSignal.at_append_lt _ _ _ _ hlenQR hAne t (fun r hr => htu.trans (hgt r hr)),
        PointSegmentSignal.at_snoc_lt Q.timePoints Q.values u r0 r1 hQlen hQne t htu]
    · rw [PointSegmentSignal.at_append_lt _ _ _ _ hlenQR hAne u hgt,
        PointSegmentSignal.at_snoc_eq Q.timePoints Q.values u r0 r1 hQlen hQu, hr0]
    -- after `u` the result is `s` again
    · refine PointSegmentSignal.suffix_at s hs j u hjle ha hj1 hj2 _ _ hlenQR hAne hAle
        after haf ?_
      intro t ht
      rw [PointSegmentSignal.at_snoc_gt Q.timePoints Q.values u r0 r1 hQlen hQu t ht, hr1]
  · -- no new point at the upper end
    simp only [hA, if_false, List.append_nil]
    have hnone : r0 = value ∧ r1 = value := by
      have := mt haddR.mpr hA
      simp at this; exact this
    have hafter : after = value := hr1 ▸ hnone.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine PointSegmentSignal.isValid_append_drop s hs j hj1 hj2 _ _ hQv ?_ ?_
      · intro x hx b hb
        exact (hQu x hx).trans (hnext b hb)
      · rw [hQlast, ← hVSlast, hafter]
    · intro t ht0 htu
      rw [PointSegmentSignal.at_append_lt _ _ _ _ hQlen hQne t (fun r hr => htu.trans (hgt r hr))]
    · rw [PointSegmentSignal.at_append_lt _ _ _ _ hQlen hQne u hgt, hQabove u hlu, ← hr0, hnone.1]
    · refine PointSegmentSignal.suffix_at s hs j u hjle ha hj1 hj2 _ _ hQlen hQne
        (fun x hx => (hQu x hx).le) after haf ?_
      intro t ht
      rw [hQabove t (hlu.trans ht), hafter]


/-- `set` on an interval with distinct ends. -/
private theorem aux_set_ne (s : PointSegmentSignal T) (hs : s.IsValid) (lb : T) (up : WithTop T)
    (lc rc : Bool) (value : Bool) (h0 : 0 ≤ lb)
    (hne : STLInterval.emptyBounds lb up lc rc = false)
    (hlt : (lb : WithTop T) ≠ up) : -- --- CONCL ---
    (s.step_setBounds lb up lc rc value).IsValid ∧ ∀ t : T, 0 ≤ t →
      (STLInterval.IsInBounds lb up lc rc t → (s.step_setBounds lb up lc rc value).at t = value) ∧
      (¬ STLInterval.IsInBounds lb up lc rc t → (s.step_setBounds lb up lc rc value).at t = s.at t)
      := by -- --- PROOF ---
  obtain ⟨hQv, hQle, hdrop, hbelow, hatlb, habove, hlast⟩ := aux_ls_spec s hs lb h0 lc value
  induction up using WithTop.recTopCoe with
  | top =>
    have hR : s.step_setBounds lb ⊤ lc rc value = aux_lowerPrefix s lb lc value := by
      have hj : (s.atIdx (⊤ : WithTop T)).2 = s.timePoints.length := by
        simp only [PointSegmentSignal.atIdx, le_top, decide_true]
        rw [List.takeWhile_eq_self_iff.mpr (fun _ _ => rfl)]
      have hvl : s.values.length = 2 * s.timePoints.length := hs.2.1
      unfold PointSegmentSignal.step_setBounds aux_lowerPrefix
      simp only [TimeOrder.isEqvTop_iff_eq, TimeOrder.eqv_iff_eq, hne, hlt, Bool.false_eq_true,
        if_false, ne_eq, not_true_eq_false, and_false, hj,
        List.drop_length, hvl.symm ▸ (List.drop_length (l := s.values)), List.append_nil]
    -- with no upper end the result is the lower prefix alone
    rw [hR]
    refine ⟨hQv, fun t ht => ?_⟩
    rcases lt_trichotomy t lb with h | h | h
    · have hnm : ¬ STLInterval.IsInBounds lb ⊤ lc rc t := by
        rintro ⟨h1 | ⟨-, h1⟩, -⟩
        · exact absurd h1 (not_lt.mpr h.le)
        · exact absurd h1 h.ne
      exact ⟨fun hm => absurd hm hnm, fun _ => hbelow t ht h⟩
    -- at `lb` itself
    · subst h
      cases lc
      · have hnm : ¬ STLInterval.IsInBounds t ⊤ false rc t := by
          rintro ⟨h1 | ⟨h1, -⟩, -⟩
          · exact lt_irrefl _ h1
          · exact Bool.noConfusion h1
        exact ⟨fun hm => absurd hm hnm, fun _ => by simpa using hatlb⟩
      · have hm : STLInterval.IsInBounds t ⊤ true rc t := ⟨Or.inr ⟨rfl, rfl⟩,
          Or.inl (WithTop.coe_lt_top t)⟩
        exact ⟨fun _ => by simpa using hatlb, fun hnm => absurd hm hnm⟩
    · have hm : STLInterval.IsInBounds lb ⊤ lc rc t := ⟨Or.inl h, Or.inl (WithTop.coe_lt_top t)⟩
      exact ⟨fun _ => habove t h, fun hnm => absurd hm hnm⟩
  | coe u =>
    have hlu : lb < u := by
      have h1 : ¬ ((u : WithTop T) < lb ∨ ((u : WithTop T) = lb ∧ ¬(lc = true ∧ rc = true))) := by
        simpa [STLInterval.emptyBounds] using hne
      have h2 : lb ≤ u := by
        by_contra hc; exact h1 (Or.inl (by exact_mod_cast not_le.mp hc))
      exact h2.lt_of_ne (fun h => hlt (by rw [h]))
    have hu0 : 0 ≤ u := h0.trans hlu.le
    -- the values the interval's last piece contributes, named once
    obtain ⟨M, hM⟩ : ∃ M : List Bool, M = (if rc = true then
        [value, s.succIntervalValue (s.atIdx (u : WithTop T)).2]
        else [(s.atIdx (u : WithTop T)).1, s.succIntervalValue (s.atIdx (u : WithTop T)).2]) :=
      ⟨_, rfl⟩
    -- `set` is the lower prefix, the upper point and the tail from `ub`
    have hR : s.step_setBounds lb (u : WithTop T) lc rc value =
        ⟨(aux_lowerPrefix s lb lc value).timePoints ++
          (if (M.any (fun v => v ≠ value)) = true then [u] else []) ++
          s.timePoints.drop (s.atIdx (u : WithTop T)).2,
        (aux_lowerPrefix s lb lc value).values ++
          (if (M.any (fun v => v ≠ value)) = true then M else []) ++
          s.values.drop (2 * (s.atIdx (u : WithTop T)).2)⟩ := by
      subst hM
      -- unfold `set` and regroup the appended lists
      unfold PointSegmentSignal.step_setBounds aux_lowerPrefix
      simp only [TimeOrder.isEqvTop_iff_eq, TimeOrder.eqv_iff_eq, hne, hlt, Bool.false_eq_true,
        if_false, ne_eq, WithTop.coe_ne_top,
        not_false_eq_true, and_true, WithTop.untopD_coe, List.append_assoc]
    subst hM
    obtain ⟨hRv, hRlt, hRu, hRgt⟩ :=
      aux_us_spec s hs (aux_lowerPrefix s lb lc value) lb u h0 hlu rc value
      hQv hQle habove hlast _ _ _ _ _ rfl rfl rfl rfl Iff.rfl _ hR
    refine ⟨hRv, fun t ht => ?_⟩
    have hlu' : (lb : WithTop T) < (u : WithTop T) := WithTop.coe_lt_coe.mpr hlu
    rcases lt_trichotomy t lb with h | h | h
    · -- before the interval
      have hnm : ¬ STLInterval.IsInBounds lb (u : WithTop T) lc rc t := by
        rintro ⟨h1 | ⟨-, h1⟩, -⟩
        · exact absurd h1 (not_lt.mpr h.le)
        · exact absurd h1 h.ne
      exact ⟨fun hm => absurd hm hnm, fun _ => by rw [hRlt t ht (h.trans hlu)]; exact hbelow t ht h⟩
    · -- at the lower end
      subst h
      have hat : (s.step_setBounds t (u : WithTop T) lc rc value).at t =
          if lc = true then value else
          s.at t := by
        rw [hRlt t ht hlu]; exact hatlb
      cases lc
      · have hnm : ¬ STLInterval.IsInBounds t (u : WithTop T) false rc t := by
          rintro ⟨h1 | ⟨h1, -⟩, -⟩
          · exact lt_irrefl _ h1
          · exact Bool.noConfusion h1
        exact ⟨fun hm => absurd hm hnm, fun _ => by simpa using hat⟩
      · have hm : STLInterval.IsInBounds t (u : WithTop T) true rc t :=
          ⟨Or.inr ⟨rfl, rfl⟩, Or.inl hlu'⟩
        exact ⟨fun _ => by simpa using hat, fun hnm => absurd hm hnm⟩
    · rcases lt_trichotomy t u with h' | h' | h'
      · -- inside
        have hm : STLInterval.IsInBounds lb (u : WithTop T) lc rc t :=
          ⟨Or.inl h, Or.inl (WithTop.coe_lt_coe.mpr h')⟩
        refine ⟨fun _ => ?_, fun hnm => absurd hm hnm⟩
        rw [hRlt t ht h', habove t h]
      · -- at the upper end
        subst h'
        have hat := hRu
        cases rc
        · have hnm : ¬ STLInterval.IsInBounds lb (t : WithTop T) lc false t := by
            rintro ⟨-, h1 | ⟨h1, -⟩⟩
            · exact lt_irrefl _ h1
            · exact Bool.noConfusion h1
          exact ⟨fun hm => absurd hm hnm, fun _ => by simpa using hat⟩
        · have hm : STLInterval.IsInBounds lb (t : WithTop T) lc true t :=
            ⟨Or.inl h, Or.inr ⟨rfl, rfl⟩⟩
          exact ⟨fun _ => by simpa using hat, fun hnm => absurd hm hnm⟩
      · -- after the interval
        have hnm : ¬ STLInterval.IsInBounds lb (u : WithTop T) lc rc t := by
          rintro ⟨-, h1 | ⟨-, h1⟩⟩
          · exact absurd (WithTop.coe_lt_coe.mp h1) (not_lt.mpr h'.le)
          · exact h'.ne (WithTop.coe_inj.mp h1).symm
        exact ⟨fun hm => absurd hm hnm, fun _ => hRgt t h'⟩


/-- `step_setBounds` sets the interval to `value` and changes nothing else, and keeps the signal
valid. -/
private theorem PointSegmentSignal.aux_setBounds_spec (s : PointSegmentSignal T) (hs : s.IsValid)
    (lb : T) (up : WithTop T) (lc rc : Bool) (hI : 0 ≤ lb) (value : Bool) : -- --- CONCL ---
    (s.step_setBounds lb up lc rc value).IsValid ∧ ∀ t : T, 0 ≤ t →
      (STLInterval.IsInBounds lb up lc rc t → (s.step_setBounds lb up lc rc value).at t = value) ∧
      (¬ STLInterval.IsInBounds lb up lc rc t →
        (s.step_setBounds lb up lc rc value).at t = s.at t) := by -- --- PROOF ---
  by_cases hne : STLInterval.emptyBounds lb up lc rc = true
  · have hset : s.step_setBounds lb up lc rc value = s := by
      unfold PointSegmentSignal.step_setBounds; rw [if_pos hne]
    rw [hset]
    exact ⟨hs, fun t _ => ⟨fun hm => absurd hm (STLInterval.not_memBounds_of_emptyBounds _ _ _ _
        t hne),
      fun _ => rfl⟩⟩
  · have hne' : STLInterval.emptyBounds lb up lc rc = false := by simpa using hne
    by_cases hsing : (lb : WithTop T) = up
    · have hset : s.step_setBounds lb up lc rc value = s.setPoint lb value := by
        unfold PointSegmentSignal.step_setBounds
        rw [if_neg hne, if_pos ((TimeOrder.isEqvTop_iff_eq _ _).2 hsing)]
      -- a single time is `aux_setPoint`
      rw [hset]
      obtain ⟨hv, hat⟩ := PointSegmentSignal.setPoint_spec s hs lb hI value
      refine ⟨hv, fun t ht => ?_⟩
      have h1 : ¬ (up < (lb : WithTop T) ∨ (up = lb ∧ ¬(lc = true ∧ rc = true))) := by
        simpa [STLInterval.emptyBounds] using hne'
      have hlcrc : lc = true ∧ rc = true := by
        by_contra hc; exact h1 (Or.inr ⟨hsing.symm, hc⟩)
      have hmem : STLInterval.IsInBounds lb up lc rc t ↔ t = lb := by
        rw [← hsing]
        simp only [STLInterval.IsInBounds, hlcrc.1, hlcrc.2, true_and, WithTop.coe_lt_coe,
            WithTop.coe_inj]
        constructor
        · rintro ⟨h | h, h' | h'⟩
          · exact absurd h (not_lt.mpr h'.le)
          · exact absurd h' h.ne'
          · exact absurd h (ne_of_lt h')
          · exact h
        · intro h; exact ⟨Or.inr h, Or.inr h⟩
      -- the interval contains exactly the time `lb`
      rw [hat t ht]
      constructor
      · intro hm; rw [if_pos (hmem.mp hm)]
      · intro hm; rw [if_neg (fun h => hm (hmem.mpr h))]
    -- distinct ends
    · exact aux_set_ne s hs lb up lc rc value hI hne' hsing |> fun ⟨hv, h⟩ => ⟨hv, h⟩

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.set_spec (s : PointSegmentSignal ℝ) (hs : s.IsValid)
    (I : STLInterval ℝ) (value : Bool) : -- --- CONCL ---
    (s.set I value).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (t ∈ I.set → (s.set I value).at t = value) ∧
      (t ∉ I.set → (s.set I value).at t = s.at t) := by -- --- PROOF ---
  obtain ⟨hv, h⟩ := PointSegmentSignal.aux_setBounds_spec s hs I.lowerBound I.upperBound
    I.lowerClosed I.upperClosed (STLInterval.zero_le_lowerBound I) value
  refine ⟨hv, fun t ht => ?_⟩
  rw [STLInterval.set_iff_memBounds I t]
  exact h t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
