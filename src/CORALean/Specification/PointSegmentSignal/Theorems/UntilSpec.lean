module

public import CORALean.Specification.PointSegmentSignal.Operations.Until
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsStretch
public import CORALean.Specification.PointSegmentSignal.Theorems.IntervalUntilSpec
public import CORALean.Specification.STLInterval.Theorems.ZeroLeOfMemSet

@[expose] public section

/-!
# The until of two signals

For valid signals over `ℝ` and an until interval with lower bound `≥ 0`, `until(lhs,interval,rhs)`
is valid and, at a time `t ≥ 0`, `true` iff there is a time `t'` with `t' - t` in the interval, the
right-hand side `true` at `t'` and the left-hand side `true` strictly between `t` and `t'`. The
left-hand side is not asked to hold at `t` itself.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `until` is true where the right-hand side holds at a time in the interval after, the
left-hand side in between. -/
theorem PointSegmentSignal.until_spec (lhs rhs : PointSegmentSignal ℝ) (hl : lhs.IsValid)
    (hr : rhs.IsValid) (U : STLInterval) (hU : ∀ f, U.fieldsOf = some f → 0 ≤ f.lower) :
    (lhs.until U rhs).IsValid ∧ ∀ t : ℝ, 0 ≤ t → ((lhs.until U rhs).at t = true ↔
      ∃ t', t' - t ∈ U.set ∧ rhs.at t' = true ∧
        ∀ x, t < x → x < t' → lhs.at x = true) := by -- --- PROOF ---
  -- the intervals of the two signals
  obtain ⟨hL0, hL1, -⟩ := lhs.findIntervals_spec hl id
  obtain ⟨hR0, hR1, -⟩ := rhs.findIntervals_spec hr id
  obtain ⟨hv, h⟩ := PointSegmentSignal.intervalUntil_spec lhs.findIntervals rhs.findIntervals U
    hL0 hR0 hU
  refine ⟨hv, fun t ht => ?_⟩
  show (PointSegmentSignal.intervalUntil lhs.findIntervals U rhs.findIntervals).at t = true ↔ _
  rw [(h t ht)]
  constructor
  · rintro (⟨L, hL', R, hR', t', ht', hcr, hcl, hu, hne⟩ | ⟨h0, R, hR', htR⟩)
    · -- a pair of intervals reaches from `t` to `t'`
      have hle : 0 ≤ t' - t := STLInterval.zero_le_of_mem_set U hU _ hu
      have hlt : t < t' := lt_of_le_of_ne (by linarith) (Ne.symm hne)
      refine ⟨t', hu, ?_, ?_⟩
      · exact (hR1 t' (by linarith)).1 ⟨R, hR', ht'⟩
      · exact (lhs.findIntervals_stretch hl t t' ht hlt).2 ⟨L, hL', hcl, hcr⟩
    · exact ⟨t, by simpa using h0, (hR1 t ht).1 ⟨R, hR', htR⟩,
        fun x h1 h2 => absurd h1 (not_lt.2 h2.le)⟩
  · rintro ⟨t', hu, hrt, hall⟩
    have hle : 0 ≤ t' - t := STLInterval.zero_le_of_mem_set U hU _ hu
    rcases lt_or_eq_of_le (show t ≤ t' by linarith) with hlt | heq
    · -- a left-hand side interval reaches from `t` to `t'`
      obtain ⟨L, hL', hcl, hcr⟩ := (lhs.findIntervals_stretch hl t t' ht hlt).1 hall
      obtain ⟨R, hR', ht'⟩ := (hR1 t' (by linarith)).2 hrt
      exact Or.inl ⟨L, hL', R, hR', t', ht', hcr, hcl, hu, hlt.ne'⟩
    · -- the right-hand side holds at `t` itself, and `0` is in the interval
      subst heq
      obtain ⟨R, hR', htR⟩ := (hR1 t ht).2 hrt
      exact Or.inr ⟨by simpa using hu, R, hR', htR⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
