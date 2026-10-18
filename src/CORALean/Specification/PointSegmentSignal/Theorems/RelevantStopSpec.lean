module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.RelevantStop
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CellBetween
public import CORALean.Specification.PointSegmentSignal.Theorems.CellLeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.CellLt
public import CORALean.Specification.PointSegmentSignal.Theorems.CellMono
public import CORALean.Specification.PointSegmentSignal.Theorems.CellTimePoint
public import CORALean.Specification.PointSegmentSignal.Theorems.TakeWhileLePos
public import Mathlib.Order.Interval.Set.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.SuccTimeAtValIdxOfLt
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx

@[expose] public section

/-!
# The last value an interval reaches

For a valid signal in dense time without a last moment and an upper end `ub ≥ 0`, the index `stop`
of `priv_relevantValueIdx` is within `values`; every time of the interval reads a value before it;
and from any time of the interval there is a later one that reads the value `stop`, one-based, the
last.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The last value of an interval is the one read at its right end, or just before it. -/
theorem PointSegmentSignal.relevantStop_spec {T : Type} [LinearOrder T] [Zero T] [DenselyOrdered T]
    [NoMaxOrder T] (s : PointSegmentSignal T) (hs : s.IsValid) (ub : WithTop T)
    (hub0 : ((0 : T) : WithTop T) ≤ ub) (rc : Bool) : -- --- STMT ---
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
      simp only [PointSegmentSignal.relevantStop]
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
      rw [hstop, s.cell_between hs (s.timePoints.length - 1) (by omega) t ht0 hlast
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
      simp only [PointSegmentSignal.relevantStop, WithTop.coe_le_coe, List.getD_eq_getElem?_getD,
        ha2, Option.getD_some, WithTop.coe_inj]
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
        rw [← hE, ← ha2']; exact s.cell_timePoint hs (j - 1) hja (by rw [ha2', hE]; exact hu0)
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
          rw [s.cell_between hs (j - 2) (by omega) t ht0 (lt_of_le_of_lt (le_max_right _ _) ht1)
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
        s.cell_between hs (j - 1) hja u hu0 (by rw [ha2']; exact hlt) hnx
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
          rw [s.cell_between hs (j - 1) hja t ht0
            (by rw [ha2']; exact lt_of_le_of_lt (le_max_right _ _) ht1)
            (fun h' => lt_trans ht2 (hnx h'))]
          omega
        · refine ⟨u, hup x h, Or.inr ⟨rfl, rfl⟩, ?_⟩
          omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
