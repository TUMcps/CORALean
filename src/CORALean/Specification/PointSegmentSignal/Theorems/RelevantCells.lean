module

public import CORALean.Specification.PointSegmentSignal.Theorems.CellLt
public import CORALean.Specification.PointSegmentSignal.Theorems.CellMono
public import CORALean.Specification.PointSegmentSignal.Theorems.ExistsCellEq
public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.RelevantStart
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.SuccTimeAtValIdxOfGe
public import CORALean.Specification.PointSegmentSignal.Theorems.CellGeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.TakeWhileLePos
public import CORALean.Specification.PointSegmentSignal.Theorems.PrecTimeAtValIdxSucc
public import CORALean.Specification.PointSegmentSignal.Operations.RelevantStop
public import CORALean.Specification.PointSegmentSignal.Theorems.CellLeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.SuccTimeAtValIdxOfLt
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx
public import CORALean.Specification.STLInterval.Definitions.IsInBounds
public import CORALean.Specification.STLInterval.Operations.Basic
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

/-!
# The values an interval reaches

In dense time without a last moment, for a valid signal and a nonempty interval with lower bound `lb
≥ 0`, the stored values (zero-based) from `start - 1` up to before `stop`, the range of
`priv_relevantValueIdx`, are exactly those read at some time of the interval.

## Inputs
* `T` – time type
* `s` – signal
* `lb` – interval lower bound
* `ub` – interval upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed
* `m` – value index

## Hypotheses
* `hs` – the signal is valid
* `h0` – the lower bound is nonnegative
* `hne` – the interval is nonempty

## Conclusion
* the value lies between start and stop iff some time of the interval reads it
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The point value of the `k`-th time point. -/
private theorem PointSegmentSignal.aux_cell_timePoint {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (k : ℕ) (hk : k < s.timePoints.length)
    (h0 : 0 ≤ s.timePoints[k]) : -- --- CONCL ---
    s.cell s.timePoints[k] = 2 * k := by -- --- PROOF ---
  have hlen := hs.2.1
  have hb : 2 * k < s.values.length := by omega
  have hk' : (2 * k) / 2 < s.timePoints.length := by omega
  have hpre := s.precTimeAtValIdx_succ (2 * k) (by omega)
  have hsucc := s.succTimeAtValIdx_of_lt (2 * k) (by omega)
  refine le_antisymm ?_ ?_
  · refine (s.cell_le_iff hs _ h0 (2 * k) hb).2 (Or.inr ⟨?_, ?_⟩)
    · simp [hsucc]
    · simp [hsucc]
      congr 1
      omega
  · refine (s.cell_ge_iff hs _ h0 (2 * k) hb).2 (Or.inr ⟨?_, ?_⟩)
    · simp [hpre]
    · simp [hpre]


/-- The interval value after the `k`-th time point. -/
private theorem PointSegmentSignal.aux_cell_between {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (k : ℕ) (hk : k < s.timePoints.length) (t : T)
    (h0 : 0 ≤ t) (h1 : s.timePoints[k] < t)
    (h2 : ∀ h : k + 1 < s.timePoints.length, t < s.timePoints[k + 1]) : -- --- CONCL ---
    s.cell t = 2 * k + 1 := by -- --- PROOF ---
  have hlen := hs.2.1
  have hb : 2 * k + 1 < s.values.length := by omega
  have hpre := s.precTimeAtValIdx_succ (2 * k + 1) (by omega)
  refine le_antisymm ?_ ?_
  · refine (s.cell_le_iff hs _ h0 (2 * k + 1) hb).2 (Or.inl ?_)
    by_cases hk2 : k + 1 < s.timePoints.length
    · rw [s.succTimeAtValIdx_of_lt (2 * k + 1) (by omega)]
      simpa [show (2 * k + 1 + 1) / 2 = k + 1 by omega] using h2 hk2
    · rw [s.succTimeAtValIdx_of_ge (2 * k + 1) (by omega)]
      exact WithTop.coe_lt_top _
  · refine (s.cell_ge_iff hs _ h0 (2 * k + 1) hb).2 (Or.inl ?_)
    simpa [hpre, show (2 * k + 1) / 2 = k by omega] using h1


/-- The last value of an interval is the one read at its right end, or just before it. -/
private theorem PointSegmentSignal.aux_relevantStop_spec {T : Type} [LinearOrder T] [Zero T]
    [DenselyOrdered T] [NoMaxOrder T] (s : PointSegmentSignal T) (hs : s.IsValid) (ub : WithTop T)
    (hub0 : ((0 : T) : WithTop T) ≤ ub) (rc : Bool) : -- --- CONCL ---
    s.relevantStop ub rc ≤ s.values.length ∧
    (∀ t : T, 0 ≤ t → ((t : WithTop T) < ub ∨ (rc = true ∧ (t : WithTop T) = ub)) →
      s.cell t < s.relevantStop ub rc) ∧
    (∀ x : T, 0 ≤ x → ((x : WithTop T) < ub ∨ (rc = true ∧ (x : WithTop T) = ub)) →
      ∃ t : T, x ≤ t ∧ ((t : WithTop T) < ub ∨ (rc = true ∧ (t : WithTop T) = ub)) ∧
        s.cell t + 1 = s.relevantStop ub rc) := by -- --- PROOF ---
  have hlen := hs.2.1
  induction ub using WithTop.recTopCoe with
  | top =>
    -- no upper end: all points are `≤ inf`, and the last value is the last interval value
    have hstop : s.relevantStop ⊤ rc = 2 * s.timePoints.length := by
      simp only [TimeOrder.isEqvTop_iff_eq, PointSegmentSignal.relevantStop]
      rw [List.takeWhile_eq_self_iff.2 (by simp)]
      simp
    have hn : 1 ≤ s.timePoints.length := List.length_pos_iff.2 hs.1
    refine ⟨by omega, fun t ht _ => ?_, fun x hx _ => ?_⟩
    · have := s.cell_lt hs t ht
      omega
    · obtain ⟨t, ht⟩ := exists_gt (max x s.timePoints[s.timePoints.length - 1])
      have hlast : s.timePoints[s.timePoints.length - 1] < t :=
        lt_of_le_of_lt (le_max_right _ _) ht
      have ht0 : 0 ≤ t := (hx.trans (le_max_left _ _)).trans ht.le
      refine ⟨t, (le_max_left _ _).trans ht.le, Or.inl (WithTop.coe_lt_top _), ?_⟩
      rw [hstop, s.aux_cell_between hs (s.timePoints.length - 1) (by omega) t ht0 hlast
        (fun h => absurd h (by omega))]
      omega
  | coe u =>
    have hu0 : 0 ≤ u := WithTop.coe_le_coe.1 hub0
    -- the time points at or before `u`
    obtain ⟨hj1, hj2, ⟨a2, ha2, hale⟩, hnext⟩ := PointSegmentSignal.takeWhile_le_pos s hs u hu0
    have hstop : s.relevantStop (u : WithTop T) rc = if a2 = u then
        (if rc = true then 2 * (s.timePoints.takeWhile (· ≤ u)).length - 1
          else 2 * (s.timePoints.takeWhile (· ≤ u)).length - 2)
        else 2 * (s.timePoints.takeWhile (· ≤ u)).length := by
      simp only [TimeOrder.isEqvTop_iff_eq, PointSegmentSignal.relevantStop, WithTop.coe_le_coe,
        List.getD_eq_getElem?_getD, ha2, Option.getD_some, WithTop.coe_inj]
    have hja : (s.timePoints.takeWhile (· ≤ u)).length - 1 < s.timePoints.length := by omega
    have ha2' : s.timePoints[(s.timePoints.takeWhile (· ≤ u)).length - 1] = a2 := by
      rw [List.getElem?_eq_getElem hja] at ha2; exact Option.some.inj ha2
    generalize (s.timePoints.takeWhile (· ≤ u)).length = j at *
    -- the time point after those `≤ u`, if there is one, is `> u`
    have hnx : ∀ h : j - 1 + 1 < s.timePoints.length, u < s.timePoints[j - 1 + 1] := fun h =>
      hnext _ ((congrArg (fun n => s.timePoints[n]?) (show j = j - 1 + 1 by omega)).trans
        (List.getElem?_eq_getElem h))
    -- a time of the interval is `≤ u`, so reads at most what `u` reads
    have hmono : ∀ t : T, 0 ≤ t → t ≤ u → s.cell t ≤ s.cell u := fun t ht h =>
      s.cell_mono hs t u ht h
    have hup : ∀ t : T, ((t : WithTop T) < (u : WithTop T) ∨
        (rc = true ∧ (t : WithTop T) = (u : WithTop T))) → t ≤ u := fun t h => by
      rcases h with h | ⟨-, h⟩
      · exact (WithTop.coe_lt_coe.1 h).le
      · exact (WithTop.coe_inj.1 h).le
    by_cases hE : a2 = u
    · -- the upper end is the time point
      rw [if_pos hE] at hstop
      have hcu : s.cell u = 2 * (j - 1) := by
        rw [← hE, ← ha2']; exact s.aux_cell_timePoint hs (j - 1) hja (by rw [ha2', hE]; exact hu0)
      cases rc
      · -- open: the values before the point
        simp only [Bool.false_eq_true, if_false] at hstop
        rw [hstop]
        -- a time before `u` shows that `u` is not the first time point `0`
        have hj2' : ∀ y : T, 0 ≤ y → y < u → 2 ≤ j := fun y hy hyu => by
          by_contra hlt2
          have h00 : s.timePoints[0]? = some 0 := by
            simpa [List.head?_eq_getElem?] using hs.2.2.1
          have hj1' : j - 1 = 0 := by omega
          rw [hj1', h00] at ha2
          have h0u : (0 : T) = u := (Option.some.inj ha2).trans hE
          exact absurd (hy.trans_lt hyu) (by rw [← h0u]; exact lt_irrefl _)
        have hopen : ∀ t : T, ((t : WithTop T) < (u : WithTop T) ∨
            (false = true ∧ (t : WithTop T) = (u : WithTop T))) → t < u := fun t h => by
          rcases h with h | ⟨h, -⟩
          · exact WithTop.coe_lt_coe.1 h
          · exact absurd h (by simp)
        refine ⟨by omega, fun t ht h => ?_, fun x hx h => ?_⟩
        · -- the values before `u` read at most `2 j - 3`
          have htu := hopen t h
          have hj := hj2' t ht htu
          have hb : 2 * j - 3 < s.values.length := by omega
          have := (s.cell_le_iff hs t ht (2 * j - 3) hb).2 (Or.inl (by
            rw [s.succTimeAtValIdx_of_lt (2 * j - 3) (by omega)]
            simp only [show (2 * j - 3 + 1) / 2 = j - 1 by omega, ha2', hE]
            exact WithTop.coe_lt_coe.2 htu))
          omega
        · -- a time just before `u`, after the time point before `a2`
          have hxu := hopen x h
          have hj := hj2' x hx hxu
          have hpt : s.timePoints[j - 2] < u := by
            have := List.pairwise_iff_getElem.1 hs.2.2.2.1 (j - 2) (j - 1) (by omega) hja (by omega)
            rwa [ha2', hE] at this
          obtain ⟨t, ht1, ht2⟩ := exists_between (max_lt hxu hpt)
          have ht0 : 0 ≤ t := hx.trans ((le_max_left _ _).trans ht1.le)
          refine ⟨t, (le_max_left _ _).trans ht1.le, Or.inl (WithTop.coe_lt_coe.2 ht2), ?_⟩
          rw [s.aux_cell_between hs (j - 2) (by omega) t ht0 (lt_of_le_of_lt (le_max_right _ _) ht1)
            (fun h' => by
              have e : s.timePoints[j - 2 + 1] = u := by
                simp only [show j - 2 + 1 = j - 1 by omega]
                exact ha2'.trans hE
              rwa [e])]
          omega
      · -- closed: the point value
        simp only [if_true] at hstop
        rw [hstop]
        refine ⟨by omega, fun t ht h => ?_, fun x hx h => ?_⟩
        · have := hmono t ht (hup t h)
          omega
        · refine ⟨u, hup x h, Or.inr ⟨rfl, rfl⟩, ?_⟩
          omega
    · -- the upper end is inside the interval value after the time point `a2`
      rw [if_neg hE] at hstop
      have hlt : a2 < u := lt_of_le_of_ne hale hE
      have hcu : s.cell u = 2 * (j - 1) + 1 :=
        s.aux_cell_between hs (j - 1) hja u hu0 (by rw [ha2']; exact hlt) hnx
      rw [hstop]
      refine ⟨by omega, fun t ht h => ?_, fun x hx h => ?_⟩
      · have := hmono t ht (hup t h)
        omega
      · cases rc
        · -- open: a time inside the interval value
          have hxu : x < u := by
            rcases h with h | ⟨h, -⟩
            · exact WithTop.coe_lt_coe.1 h
            · exact absurd h (by simp)
          obtain ⟨t, ht1, ht2⟩ := exists_between (max_lt hxu hlt)
          have ht0 : 0 ≤ t := hx.trans ((le_max_left _ _).trans ht1.le)
          refine ⟨t, (le_max_left _ _).trans ht1.le, Or.inl (WithTop.coe_lt_coe.2 ht2), ?_⟩
          rw [s.aux_cell_between hs (j - 1) hja t ht0
            (by rw [ha2']; exact lt_of_le_of_lt (le_max_right _ _) ht1)
            (fun h' => lt_trans ht2 (hnx h'))]
          omega
        · refine ⟨u, hup x h, Or.inr ⟨rfl, rfl⟩, ?_⟩
          omega


/-- The first value of an interval is the one read at its left end, or just after it. -/
private theorem PointSegmentSignal.aux_relevantStart_spec {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (lb : T) (h0 : 0 ≤ lb)
    (lc : Bool) : -- --- CONCL ---
    1 ≤ s.relevantStart lb lc ∧ s.relevantStart lb lc ≤ s.values.length ∧
    (∀ t : T, 0 ≤ t → (lb < t ∨ (lc = true ∧ t = lb)) → s.relevantStart lb lc - 1 ≤ s.cell t) ∧
    (lc = true → s.cell lb = s.relevantStart lb lc - 1) ∧
    (lc = false → ∀ t : T, lb < t →
      (∀ b, s.timePoints[(s.timePoints.takeWhile (· ≤ lb)).length]? = some b → t < b) →
        s.cell t = s.relevantStart lb lc - 1) := by -- --- PROOF ---
  have hlen := hs.2.1
  -- the time points at or before `lb`
  obtain ⟨hi1, hi2, ⟨a1, ha1, hale⟩, hnext⟩ := PointSegmentSignal.takeWhile_le_pos s hs lb h0
  have hia : (s.timePoints.takeWhile (· ≤ lb)).length - 1 < s.timePoints.length := by omega
  have ha1' : s.timePoints[(s.timePoints.takeWhile (· ≤ lb)).length - 1] = a1 := by
    rw [List.getElem?_eq_getElem hia] at ha1; exact Option.some.inj ha1
  have hstart : s.relevantStart lb lc = if a1 = lb ∧ lc = true then
      2 * (s.timePoints.takeWhile (· ≤ lb)).length - 1
      else 2 * (s.timePoints.takeWhile (· ≤ lb)).length := by
    simp only [TimeOrder.eqv_iff_eq, PointSegmentSignal.relevantStart, List.getD_eq_getElem?_getD,
      ha1, Option.getD_some]
  generalize (s.timePoints.takeWhile (· ≤ lb)).length = i at *
  -- the time point after those `≤ lb`, if there is one, is `> lb`
  have hnx : ∀ h : i - 1 + 1 < s.timePoints.length, lb < s.timePoints[i - 1 + 1] := fun h =>
    hnext _ ((congrArg (fun n => s.timePoints[n]?) (show i = i - 1 + 1 by omega)).trans
      (List.getElem?_eq_getElem h))
  refine ⟨by rw [hstart]; split_ifs <;> omega, by rw [hstart]; split_ifs <;> omega, ?_, ?_, ?_⟩
  · -- every time of the interval reads at least the first value
    intro t ht hlow
    by_cases hcond : a1 = lb ∧ lc = true
    · -- the left end is a closed time point: its point value
      rw [if_pos hcond] at hstart
      rw [hstart]
      have hlo : 2 * i - 1 - 1 < s.values.length := by omega
      refine (s.cell_ge_iff hs t ht _ hlo).2 ?_
      rw [s.precTimeAtValIdx_succ (2 * i - 1 - 1) (by omega)]
      simp only [show (2 * i - 1 - 1) / 2 = i - 1 by omega,
        show (2 * i - 1 - 1) % 2 = 0 by omega, decide_true, true_and, ha1']
      rcases hlow with h | ⟨-, h⟩
      · exact Or.inl (hcond.1 ▸ h)
      · exact Or.inr (hcond.1 ▸ h)
    · -- otherwise the value after the time point `a1`, which is before `t`
      rw [if_neg hcond] at hstart
      rw [hstart]
      have hlo : 2 * i - 1 < s.values.length := by omega
      refine (s.cell_ge_iff hs t ht _ hlo).2 ?_
      rw [s.precTimeAtValIdx_succ (2 * i - 1) (by omega)]
      simp only [show (2 * i - 1) / 2 = i - 1 by omega, ha1']
      refine Or.inl ?_
      rcases hlow with h | ⟨hl, h⟩
      · exact lt_of_le_of_lt hale h
      · exact h ▸ lt_of_le_of_ne hale (fun e => hcond ⟨e, hl⟩)
  · -- a closed left end reads the value of the time point, or just after it
    intro hl
    by_cases hcond : a1 = lb
    · rw [if_pos ⟨hcond, hl⟩] at hstart
      rw [hstart, ← hcond, ← ha1', s.aux_cell_timePoint hs (i - 1) hia
        (by rw [ha1', hcond]; exact h0)]
      omega
    · rw [if_neg (fun h => hcond h.1)] at hstart
      rw [hstart]
      have := s.aux_cell_between hs (i - 1) hia lb h0
        (by rw [ha1']; exact lt_of_le_of_ne hale hcond) (fun h => hnx h)
      omega
  · -- an open left end reads the value just after the time point before it
    intro hl t hlt hnxt
    rw [if_neg (fun h => by simp [hl] at h)] at hstart
    rw [hstart]
    have := s.aux_cell_between hs (i - 1) hia t (h0.trans hlt.le)
      (by rw [ha1']; exact lt_of_le_of_lt hale hlt)
      (fun h => hnxt _ ((congrArg (fun n => s.timePoints[n]?) (show i = i - 1 + 1 by omega)).trans
        (List.getElem?_eq_getElem h)))
    omega


-- =======================================  MAIN THEOREM  ======================================= --

/-- The values between `start` and `stop` are those some time of the interval reads. -/
theorem PointSegmentSignal.relevant_cells {T : Type} [LinearOrder T] [Zero T] [DenselyOrdered T]
    [NoMaxOrder T] (s : PointSegmentSignal T) (hs : s.IsValid) (lb : T) (ub : WithTop T)
    (lc rc : Bool) (h0 : 0 ≤ lb) (hne : STLInterval.emptyBounds lb ub lc rc = false)
    (m : ℕ) : -- --- CONCL ---
    (s.relevantStart lb lc - 1 ≤ m ∧ m < s.relevantStop ub rc ∧ m < s.values.length) ↔
      ∃ t : T, STLInterval.IsInBounds lb ub lc rc t ∧ s.cell t = m := by -- --- PROOF ---
  -- the interval is not empty: `lb ≤ ub`, and a single point is closed on both sides
  have hcond : ¬ (ub < (lb : WithTop T) ∨ (ub = (lb : WithTop T) ∧ ¬ (lc = true ∧ rc = true))) :=
    fun h => by
      have : STLInterval.emptyBounds lb ub lc rc = true := by
        unfold STLInterval.emptyBounds
        simp only [TimeOrder.isEqvTop_iff_eq]
        exact if_pos h
      rw [this] at hne
      exact absurd hne (by simp)
  have hle : (lb : WithTop T) ≤ ub := not_lt.1 fun h => hcond (Or.inl h)
  have hpt : (lb : WithTop T) = ub → lc = true ∧ rc = true := fun h => by
    by_contra hc; exact hcond (Or.inr ⟨h.symm, hc⟩)
  have hub0 : ((0 : T) : WithTop T) ≤ ub := (WithTop.coe_le_coe.2 h0).trans hle
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := s.aux_relevantStart_spec hs lb h0 lc
  obtain ⟨hp1, hp2, hp3⟩ := s.aux_relevantStop_spec hs ub hub0 rc
  constructor
  · rintro ⟨hlo, hstop, hN⟩
    -- a time just after any bound that is above `lb`
    have hgap : ∀ w : WithTop T, (lb : WithTop T) < w →
        ∃ t' : T, lb < t' ∧ (t' : WithTop T) < w := by
      intro w hw
      induction w using WithTop.recTopCoe with
      | top =>
        obtain ⟨t', ht'⟩ := exists_gt lb
        exact ⟨t', ht', WithTop.coe_lt_top _⟩
      | coe u =>
        obtain ⟨t', h1, h2⟩ := exists_between (WithTop.coe_lt_coe.1 hw)
        exact ⟨t', h1, WithTop.coe_lt_coe.2 h2⟩
    -- a time of the interval reading the first value
    obtain ⟨t₁, hl₁, hu₁, hc₁⟩ : ∃ t₁ : T, (lb < t₁ ∨ (lc = true ∧ t₁ = lb)) ∧
        ((t₁ : WithTop T) < ub ∨ (rc = true ∧ (t₁ : WithTop T) = ub)) ∧
        s.cell t₁ = s.relevantStart lb lc - 1 := by
      cases lc
      · -- an open left end: a time just after `lb`, before the next time point and the end
        have hlt : (lb : WithTop T) < ub := lt_of_le_of_ne hle fun e => by
          have := (hpt e).1; simp at this
        obtain ⟨t', ht1, ht2⟩ := hgap ub hlt
        obtain ⟨hi1, hi2, -, hnext⟩ := PointSegmentSignal.takeWhile_le_pos s hs lb h0
        by_cases hi : (s.timePoints.takeWhile (· ≤ lb)).length < s.timePoints.length
        · have hb : lb < s.timePoints[(s.timePoints.takeWhile (· ≤ lb)).length] :=
            hnext _ (List.getElem?_eq_getElem hi)
          obtain ⟨t₁, h1, h2⟩ := exists_between (lt_min ht1 hb)
          refine ⟨t₁, Or.inl h1, Or.inl ((WithTop.coe_lt_coe.2
            (lt_of_lt_of_le h2 (min_le_left _ _))).trans ht2), hs5 rfl t₁ h1 fun b hb' => ?_⟩
          have := Option.some.inj (((List.getElem?_eq_getElem hi).symm.trans hb'))
          exact this ▸ lt_of_lt_of_le h2 (min_le_right _ _)
        · exact ⟨t', Or.inl ht1, Or.inl ht2, hs5 rfl t' ht1 fun b hb' =>
            absurd (List.getElem?_eq_some_iff.1 hb').1 hi⟩
      · -- a closed left end: `lb` itself
        refine ⟨lb, Or.inr ⟨rfl, rfl⟩, ?_, (hs4 rfl)⟩
        rcases hle.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr ⟨(hpt h).2, h⟩
    have ht₁0 : 0 ≤ t₁ := by
      rcases hl₁ with h | ⟨-, h⟩
      · exact h0.trans h.le
      · exact h ▸ h0
    -- a later time of the interval reading the last value
    obtain ⟨t₂, h12, hu₂, hc₂⟩ := hp3 t₁ ht₁0 hu₁
    have hl₂ : lb < t₂ ∨ (lc = true ∧ t₂ = lb) := by
      rcases hl₁ with h | ⟨hl, h⟩
      · exact Or.inl (lt_of_lt_of_le h h12)
      · rcases (h ▸ h12 : lb ≤ t₂).lt_or_eq with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨hl, h'.symm⟩
    have ht₂0 : 0 ≤ t₂ := ht₁0.trans h12
    -- the value `m` lies between: first, last, or in the middle
    rcases (show s.cell t₁ ≤ m by omega).eq_or_lt with h1 | h1
    · exact ⟨t₁, ⟨hl₁, hu₁⟩, h1⟩
    rcases (show m ≤ s.cell t₂ by omega).eq_or_lt with h2 | h2
    · exact ⟨t₂, ⟨hl₂, hu₂⟩, h2.symm⟩
    -- a time reading the value in between lies between `t₁` and `t₂`
    obtain ⟨t, ht0, hct⟩ := s.exists_cell_eq hs m hN
    have hlt1 : t₁ < t := by
      by_contra h
      have := s.cell_mono hs t t₁ ht0 (not_lt.1 h)
      omega
    have hlt2 : t < t₂ := by
      by_contra h
      have := s.cell_mono hs t₂ t ht₂0 (not_lt.1 h)
      omega
    -- the time is in the interval, by convexity
    refine ⟨t, ⟨?_, ?_⟩, hct⟩
    · rcases hl₁ with h | ⟨-, h⟩
      · exact Or.inl (lt_trans h hlt1)
      · exact Or.inl (h ▸ hlt1)
    · rcases hu₂ with h | ⟨-, h⟩
      · exact Or.inl (lt_trans (WithTop.coe_lt_coe.2 hlt2) h)
      · exact Or.inl (h ▸ WithTop.coe_lt_coe.2 hlt2)
  · rintro ⟨t, ⟨hl, hu⟩, hct⟩
    have ht : 0 ≤ t := by
      rcases hl with h | ⟨-, h⟩
      · exact h0.trans h.le
      · exact h ▸ h0
    exact ⟨hct ▸ hs3 t ht hl, hct ▸ hp2 t ht hu, hct ▸ s.cell_lt hs t ht⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
