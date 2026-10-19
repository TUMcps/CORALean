module

public import CORALean.Specification.PointSegmentSignal.Theorems.CellLt
public import CORALean.Specification.PointSegmentSignal.Theorems.CellMono
public import CORALean.Specification.PointSegmentSignal.Theorems.ExistsCellEq
public import CORALean.Specification.PointSegmentSignal.Theorems.RelevantStartSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.RelevantStopSpec
public import CORALean.Specification.STLInterval.Definitions.MemBounds
public import CORALean.Specification.STLInterval.Operations.Basic
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

/-!
# The values an interval reaches

In dense time without a last moment, for a valid signal and a nonempty interval with lower bound `lb
≥ 0`, the stored values (zero-based) from `start - 1` up to before `stop`, the range of
`priv_relevantValueIdx`, are exactly those read at some time of the interval.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The values between `start` and `stop` are those some time of the interval reads. -/
theorem PointSegmentSignal.relevant_cells {T : Type} [LinearOrder T] [Zero T] [DenselyOrdered T]
    [NoMaxOrder T] (s : PointSegmentSignal T) (hs : s.IsValid) (lb : T) (ub : WithTop T)
    (lc rc : Bool) (h0 : 0 ≤ lb) (hne : STLInterval.emptyBounds lb ub lc rc = false)
    (m : ℕ) : -- --- CONCL ---
    (s.relevantStart lb lc - 1 ≤ m ∧ m < s.relevantStop ub rc ∧ m < s.values.length) ↔
      ∃ t : T, STLInterval.memBounds lb ub lc rc t ∧ s.cell t = m := by -- --- PROOF ---
  -- the interval is not empty: `lb ≤ ub`, and a single point is closed on both sides
  have hcond : ¬ (ub < (lb : WithTop T) ∨ (ub = (lb : WithTop T) ∧ ¬ (lc = true ∧ rc = true))) :=
    fun h => by
      have : STLInterval.emptyBounds lb ub lc rc = true := by
        unfold STLInterval.emptyBounds
        exact if_pos h
      rw [this] at hne
      exact absurd hne (by simp)
  have hle : (lb : WithTop T) ≤ ub := not_lt.1 fun h => hcond (Or.inl h)
  have hpt : (lb : WithTop T) = ub → lc = true ∧ rc = true := fun h => by
    by_contra hc; exact hcond (Or.inr ⟨h.symm, hc⟩)
  have hub0 : ((0 : T) : WithTop T) ≤ ub := (WithTop.coe_le_coe.2 h0).trans hle
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := s.relevantStart_spec hs lb h0 lc
  obtain ⟨hp1, hp2, hp3⟩ := s.relevantStop_spec hs ub hub0 rc
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
