module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Definitions.Covers
public import CORALean.Specification.FiniteSignal.Operations.Combine
public import CORALean.Specification.FiniteSignal.Operations.Indicator
public import CORALean.Specification.FiniteSignal.Theorems.AtIsSome
public import CORALean.Specification.FiniteSignal.Theorems.CombineSpec
public import CORALean.Specification.FiniteSignal.Theorems.IndicatorSpec
public import CORALean.Specification.FiniteSignal.Theorems.TimeLeDuration

@[expose] public section

/-!
# A signal or'ed with an indicator

The body of `setPossiblyTrue` and `setPossiblyFalse`: `sig | finiteSignal.indicator(dur,int,true)`
for the duration `dur` of `sig`. For a degenerate interval (`hi ≤ lo`) CORA throws in
`indicator`. Otherwise the result is a valid signal of the same duration, whose value at every
time `t` of `[0,dur]` is the old one or true where the interval marks `t` (`Covers`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

open FiniteKleeneSignalBuilder in
theorem FiniteKleeneSignalBuilder.or_indicator_spec (s : FiniteSignal ℝ Bool) (hs : s.IsValid)
    (lo hi : EReal) :
    (hi ≤ lo → (FiniteSignal.indicator? s.duration lo hi true).bind
      (fun ind => FiniteSignal.combine? (· || ·) [s, ind]) = none) ∧
    (lo < hi → ∃ s', (FiniteSignal.indicator? s.duration lo hi true).bind
        (fun ind => FiniteSignal.combine? (· || ·) [s, ind]) = some s' ∧ s'.IsValid ∧
      s'.duration = s.duration ∧ ∀ t x, s.at? t = some x → 0 ≤ t → t ≤ s.duration →
        ∃ y, s'.at? t = some y ∧
          (y = true ↔ x = true ∨ Covers s.duration t lo hi)) := by -- --- PROOF ---
  refine ⟨fun h => ?_, fun hlh => ?_⟩
  · simp [FiniteSignal.indicator?, h]
  · obtain ⟨hmem, -⟩ := FiniteSignal.time_le_duration s hs
    have h0 : 0 ≤ s.duration := hs.2.2.2.2 _ hmem
    obtain ⟨r, hr, hrv, hrd, hrat⟩ := FiniteSignal.indicator?_spec s.duration lo hi true h0 hlh
    obtain ⟨c, hc, hcv, hcd, hcat⟩ := FiniteSignal.combine?_spec (· || ·) s r hs hrv
    rw [hr, Option.bind_some, hc]
    refine ⟨c, rfl, hcv, by rw [hcd, hrd, min_self], fun t x hx h0t htd => ?_⟩
    have hy := hrat t h0t htd
    have := hcat t x _ hx hy (by
      rcases lt_or_eq_of_le htd with h | h
      · exact Or.inl ⟨h, by rw [hrd]; exact h⟩
      · exact Or.inr ⟨hrd.symm, h⟩)
    exact ⟨_, this, by simp [FiniteKleeneSignalBuilder.Covers]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
