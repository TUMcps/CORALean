module

public import CORALean.Specification.PointSegmentSignal.Operations.Until
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsSpec
public import CORALean.Specification.STLInterval.Theorems.SetLeftClosure
public import CORALean.Specification.STLInterval.Theorems.SetRightClosure
public import Mathlib.Data.EReal.Operations
public import CORALean.Specification.PointSegmentSignal.Theorems.IntervalUntilSpec
public import CORALean.Specification.STLInterval.Theorems.ZeroLeOfMemSet

@[expose] public section

/-!
# The until of two signals

For valid signals over `ℝ` and an until interval with lower bound `≥ 0`, `until(lhs,interval,rhs)`
is valid and, at a time `t ≥ 0`, `true` iff there is a time `t'` with `t' - t` in the interval, the
right-hand side `true` at `t'` and the left-hand side `true` strictly between `t` and `t'`. The
left-hand side is not asked to hold at `t` itself.

This is [1, Lemma 2] for signals of finite variability, with the strict until of [1, Sec. 2.5];
it contains [1, Lemma 1], the unitary signals being among them.

## Inputs
* `lhs` – left signal
* `rhs` – right signal
* `U` – time interval

## Hypotheses
* `hl` – the left signal is valid
* `hr` – the right signal is valid

## Conclusion
* the until is valid and true where the semantics of until says

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The signal is `true` strictly between `t` and `t'` iff one interval reaches both. -/
private theorem PointSegmentSignal.aux_findIntervals_stretch (s : PointSegmentSignal ℝ)
    (hs : s.IsValid) (t t' : ℝ) (ht : 0 ≤ t) (htt : t < t') : -- --- CONCL ---
    (∀ x, t < x → x < t' → s.at x = true) ↔
      ∃ I ∈ s.findIntervals, t ∈ I.leftClosure.set ∧ t' ∈ I.rightClosure.set := by -- --- PROOF ---
  obtain ⟨h1, h2⟩ := s.findIntervals_spec hs id
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
    | nonempty l u lc rc b c _ =>
      simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq] at hx0I hsub
      have hlx : ((Float.SoundFloatArithmetic.toReal l : ℝ) : EReal) ≤
        (((t + t') / 2 : ℝ) : EReal) := by
        rcases hx0I.1 with h | ⟨-, h⟩ <;> [exact h.le; exact h.le]
      have hux : (((t + t') / 2 : ℝ) : EReal) ≤ STLInterval.toEReal u := by
        rcases hx0I.2 with h | ⟨-, h⟩ <;> [exact h.le; exact h.le]
      -- the lower end is at most `t`, the upper end at least `t'`
      have hl : ((Float.SoundFloatArithmetic.toReal l : ℝ) : EReal) ≤ (t : EReal) := by
        by_contra h
        obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real (not_le.1 h)
        have hyt : y < t' := by
          have := EReal.coe_lt_coe_iff.1 (hy2.trans_le hlx)
          linarith [hx0.2]
        rcases (hsub y (EReal.coe_lt_coe_iff.1 hy1) hyt).1 with h' | ⟨-, h'⟩
        · exact absurd hy2 (not_lt.2 h'.le)
        · exact absurd hy2 (not_lt.2 h'.le)
      -- and the upper end is at least `t'`
      have hu : (t' : EReal) ≤ STLInterval.toEReal u := by
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
        by_cases e : ((Float.SoundFloatArithmetic.toReal l : ℝ) : EReal) = (t : EReal)
        · exact Or.inr (by simpa [STLInterval.infimum] using e.symm)
        · refine Or.inl ⟨Or.inl (lt_of_le_of_ne hl e), Or.inl ?_⟩
          exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hx0.1) hux
      -- the same for the right end
      · rw [STLInterval.set_rightClosure]
        by_cases e : STLInterval.toEReal u = (t' : EReal)
        · exact Or.inr (by simp [STLInterval.supremum, e])
        · refine Or.inl ⟨Or.inl (lt_of_le_of_lt hlx (EReal.coe_lt_coe_iff.2 hx0.2)), Or.inl ?_⟩
          exact lt_of_le_of_ne hu (Ne.symm e)
  · rintro ⟨I, hI, htl, htr⟩ x hx1 hx2
    cases I with
    | empty => exact absurd htl (by simp [STLInterval.leftClosure, STLInterval.set])
    | nonempty l u lc rc b c _ =>
      -- the interval reaches from `t` to `t'`, so it contains everything between
      rw [STLInterval.set_leftClosure] at htl
      rw [STLInterval.set_rightClosure] at htr
      have hl : ((Float.SoundFloatArithmetic.toReal l : ℝ) : EReal) ≤ (t : EReal) := by
        rcases htl with h | h
        · simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq] at h
          rcases h.1 with h' | ⟨-, h'⟩ <;> [exact h'.le; exact h'.le]
        · simp only [STLInterval.infimum, Set.mem_setOf_eq, Option.map_some,
            STLInterval.toEReal_coe, Option.some.injEq] at h
          exact h.le
      have hu : (t' : EReal) ≤ STLInterval.toEReal u := by
        rcases htr with h | h
        · simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq] at h
          rcases h.2 with h' | ⟨-, h'⟩ <;> [exact h'.le; exact h'.le]
        · simp only [STLInterval.supremum, Set.mem_setOf_eq, Option.map_some,
            Option.some.injEq] at h
          exact h.ge
      refine (h1 x (ht.trans hx1.le)).1 ⟨_, hI, ?_⟩
      simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq]
      exact ⟨Or.inl (lt_of_le_of_lt hl (EReal.coe_lt_coe_iff.2 hx1)),
        Or.inl (lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hx2) hu)⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- `until` is true where the right-hand side holds at a time in the interval after, the
left-hand side in between. -/
theorem PointSegmentSignal.until_spec (lhs rhs : PointSegmentSignal ℝ) (hl : lhs.IsValid)
    (hr : rhs.IsValid) (U : STLInterval ℝ) : -- --- CONCL ---
    (lhs.until U rhs).IsValid ∧ ∀ t : ℝ, 0 ≤ t → ((lhs.until U rhs).at t = true ↔
      ∃ t', t' - t ∈ U.set ∧ rhs.at t' = true ∧
        ∀ x, t < x → x < t' → lhs.at x = true) := by -- --- PROOF ---
  -- the intervals of the two signals
  obtain ⟨hL1, -⟩ := lhs.findIntervals_spec hl id
  obtain ⟨hR1, -⟩ := rhs.findIntervals_spec hr id
  obtain ⟨hv, h⟩ := PointSegmentSignal.intervalUntil_spec lhs.findIntervals rhs.findIntervals U
  refine ⟨hv, fun t ht => ?_⟩
  show (PointSegmentSignal.intervalUntil lhs.findIntervals U rhs.findIntervals).at t = true ↔ _
  rw [(h t ht)]
  constructor
  · rintro (⟨L, hL', R, hR', t', ht', hcr, hcl, hu, hne⟩ | ⟨h0, R, hR', htR⟩)
    · -- a pair of intervals reaches from `t` to `t'`
      have hle : 0 ≤ t' - t := STLInterval.zero_le_of_mem_set U _ hu
      have hlt : t < t' := lt_of_le_of_ne (by linarith) (Ne.symm hne)
      refine ⟨t', hu, ?_, ?_⟩
      · exact (hR1 t' (by linarith)).1 ⟨R, hR', ht'⟩
      · exact (lhs.aux_findIntervals_stretch hl t t' ht hlt).2 ⟨L, hL', hcl, hcr⟩
    · exact ⟨t, by simpa using h0, (hR1 t ht).1 ⟨R, hR', htR⟩,
        fun x h1 h2 => absurd h1 (not_lt.2 h2.le)⟩
  · rintro ⟨t', hu, hrt, hall⟩
    have hle : 0 ≤ t' - t := STLInterval.zero_le_of_mem_set U _ hu
    rcases lt_or_eq_of_le (show t ≤ t' by linarith) with hlt | heq
    · -- a left-hand side interval reaches from `t` to `t'`
      obtain ⟨L, hL', hcl, hcr⟩ := (lhs.aux_findIntervals_stretch hl t t' ht hlt).1 hall
      obtain ⟨R, hR', ht'⟩ := (hR1 t' (by linarith)).2 hrt
      exact Or.inl ⟨L, hL', R, hR', t', ht', hcr, hcl, hu, hlt.ne'⟩
    · -- the right-hand side holds at `t` itself, and `0` is in the interval
      subst heq
      obtain ⟨R, hR', htR⟩ := (hR1 t ht).2 hrt
      exact Or.inr ⟨by simpa using hu, R, hR', htR⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
