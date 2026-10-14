module

public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsSpec
public import CORALean.Specification.STLInterval.Theorems.SetLeftClosure
public import CORALean.Specification.STLInterval.Theorems.SetRightClosure
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# A stretch of `true` lies in one interval of `findIntervals`

For a valid signal over `ℝ` and times `0 ≤ t < t'`, the signal is `true` at every time strictly
between them exactly when `t` is in the left closure and `t'` in the right closure of one interval
of `findIntervals`: the interval, with its ends closed, reaches from `t` to `t'`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The signal is `true` strictly between `t` and `t'` iff one interval reaches both. -/
theorem PointSegmentSignal.findIntervals_stretch (s : PointSegmentSignal ℝ) (hs : s.IsValid)
    (t t' : ℝ) (ht : 0 ≤ t) (htt : t < t') :
    (∀ x, t < x → x < t' → s.at x = true) ↔
      ∃ I ∈ s.findIntervals, t ∈ I.leftClosure.set ∧ t' ∈ I.rightClosure.set := by -- --- PROOF ---
  obtain ⟨-, h1, h2⟩ := s.findIntervals_spec hs id
  constructor
  · intro hall
    -- the midpoint is in an interval, and so is everything between `t` and `t'`
    have hx0 : t < (t + t') / 2 ∧ (t + t') / 2 < t' := ⟨by linarith, by linarith⟩
    obtain ⟨I, hI, hx0I⟩ := (h1 _ (ht.trans hx0.1.le)).2 (hall _ hx0.1 hx0.2)
    have hsub : ∀ x, t < x → x < t' → x ∈ I.set := fun x hx1 hx2 =>
      h2 I hI _ hx0I x (ht.trans hx1.le) fun y hy0 hy1 hy2 =>
        hall y (lt_of_lt_of_le (lt_min hx0.1 hx1) hy1) (lt_of_le_of_lt hy2 (max_lt hx0.2 hx2))
    cases I with
    | empty => exact absurd hx0I (by simp [STLInterval.set])
    | nonempty l u lc rc a b c =>
      simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq] at hx0I hsub
      have hlx : l ≤ (((t + t') / 2 : ℝ) : EReal) := by
        rcases hx0I.1 with h | ⟨-, h⟩ <;> [exact h.le; exact h.le]
      have hux : (((t + t') / 2 : ℝ) : EReal) ≤ u := by
        rcases hx0I.2 with h | ⟨-, h⟩ <;> [exact h.le; exact h.le]
      -- the lower end is at most `t`, the upper end at least `t'`
      have hl : l ≤ (t : EReal) := by
        by_contra h
        obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real (not_le.1 h)
        have hyt : y < t' := by
          have := EReal.coe_lt_coe_iff.1 (hy2.trans_le hlx)
          linarith [hx0.2]
        rcases (hsub y (EReal.coe_lt_coe_iff.1 hy1) hyt).1 with h' | ⟨-, h'⟩
        · exact absurd hy2 (not_lt.2 h'.le)
        · exact absurd hy2 (not_lt.2 h'.le)
      -- and the upper end is at least `t'`
      have hu : (t' : EReal) ≤ u := by
        by_contra h
        obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real (not_le.1 h)
        have hyt : t < y := by
          have := EReal.coe_lt_coe_iff.1 (hux.trans_lt hy1)
          linarith [hx0.1]
        rcases (hsub y hyt (EReal.coe_lt_coe_iff.1 hy2)).2 with h' | ⟨-, h'⟩
        · exact absurd hy1 (not_lt.2 h'.le)
        · exact absurd hy1 (not_lt.2 h'.le)
      refine ⟨_, hI, ?_, ?_⟩
      · rw [STLInterval.set_leftClosure]
        by_cases e : l = (t : EReal)
        · exact Or.inr (by simp [STLInterval.infimum, e])
        · refine Or.inl ⟨Or.inl (lt_of_le_of_ne hl e), Or.inl ?_⟩
          exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hx0.1) hux
      -- the same for the right end
      · rw [STLInterval.set_rightClosure]
        by_cases e : u = (t' : EReal)
        · exact Or.inr (by simp [STLInterval.supremum, e])
        · refine Or.inl ⟨Or.inl (lt_of_le_of_lt hlx (EReal.coe_lt_coe_iff.2 hx0.2)), Or.inl ?_⟩
          exact lt_of_le_of_ne hu (Ne.symm e)
  · rintro ⟨I, hI, htl, htr⟩ x hx1 hx2
    cases I with
    | empty => exact absurd htl (by simp [STLInterval.leftClosure, STLInterval.set])
    | nonempty l u lc rc a b c =>
      -- the interval reaches from `t` to `t'`, so it contains everything between
      rw [STLInterval.set_leftClosure] at htl
      rw [STLInterval.set_rightClosure] at htr
      have hl : l ≤ (t : EReal) := by
        rcases htl with h | h
        · simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq] at h
          rcases h.1 with h' | ⟨-, h'⟩ <;> [exact h'.le; exact h'.le]
        · simp only [STLInterval.infimum, Set.mem_setOf_eq, Option.some.injEq] at h
          exact h.le
      have hu : (t' : EReal) ≤ u := by
        rcases htr with h | h
        · simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq] at h
          rcases h.2 with h' | ⟨-, h'⟩ <;> [exact h'.le; exact h'.le]
        · simp only [STLInterval.supremum, Set.mem_setOf_eq, Option.some.injEq] at h
          exact h.ge
      refine (h1 x (ht.trans hx1.le)).1 ⟨_, hI, ?_⟩
      simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq]
      exact ⟨Or.inl (lt_of_le_of_lt hl (EReal.coe_lt_coe_iff.2 hx1)),
        Or.inl (lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hx2) hu)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
