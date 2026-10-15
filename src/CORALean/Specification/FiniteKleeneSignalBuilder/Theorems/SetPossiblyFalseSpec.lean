module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Definitions.Represents
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.SetPossiblyFalse
public import CORALean.Specification.FiniteKleeneSignalBuilder.Theorems.OrIndicatorSpec

@[expose] public section

/-!
# What `setPossiblyFalse` computes

`setPossiblyFalse` fails exactly for a degenerate interval (`hi ≤ lo`). Otherwise it keeps the
builder valid and the other signal as it was, and `possiblyFalseSignal` becomes true at every time
`t` of `[0,dur]` that the interval marks (`Covers`), unchanged elsewhere.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

open FiniteKleeneSignalBuilder in
theorem FiniteKleeneSignalBuilder.setPossiblyFalse?_spec (b : FiniteKleeneSignalBuilder)
    (lo hi : EReal) :
    (hi ≤ lo → b.setPossiblyFalse? lo hi = none) ∧
    (lo < hi → ∀ (d : ℝ) (PT PF : ℝ → Prop), b.Represents d PT PF →
      ∃ b', b.setPossiblyFalse? lo hi = some b' ∧
        b'.Represents d PT (fun t => PF t ∨ Covers d t lo hi)) := by -- --- PROOF ---
  refine ⟨fun h => by simp [FiniteKleeneSignalBuilder.setPossiblyFalse?,
    FiniteSignal.indicator?, h], fun hlh d PT PF hb => ?_⟩
  obtain ⟨hvalid, hdur, hts⟩ := hb
  -- the signal or'ed with the indicator of the interval, and what it says at every time
  obtain ⟨s', hs', hv, hd, hat⟩ :=
    (FiniteKleeneSignalBuilder.or_indicator_spec _ hvalid.2.1 lo hi).2 hlh
  obtain ⟨ind, hind, hc⟩ := Option.bind_eq_some_iff.mp hs'
  refine ⟨{ b with possiblyFalseSignal := s' },
    by simp [FiniteKleeneSignalBuilder.setPossiblyFalse?, hind, hc],
    ⟨hvalid.1, hv, by rw [hd]; exact hvalid.2.2⟩,
    hdur, fun t h0 h1 => ?_⟩
  obtain ⟨⟨x, hx, hxi⟩, ⟨y, hy, hyi⟩⟩ := hts t h0 h1
  obtain ⟨z, hz, hzi⟩ := hat t y hy h0 (by rw [← hvalid.2.2, hdur]; exact h1)
  exact ⟨⟨x, hx, hxi⟩, ⟨z, hz, by rw [hzi, hyi, ← hvalid.2.2, hdur]⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
