module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Definitions.Represents
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.SetPossiblyTrue
public import CORALean.Specification.FiniteKleeneSignalBuilder.Theorems.OrIndicatorSpec

@[expose] public section

/-!
# What `setPossiblyTrue` computes

`setPossiblyTrue` fails exactly for a degenerate interval (`hi ≤ lo`). Otherwise it keeps the
builder valid and the other signal as it was, and `possiblyTrueSignal` becomes true at every time
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
theorem FiniteKleeneSignalBuilder.setPossiblyTrue?_spec (b : FiniteKleeneSignalBuilder)
    (lo hi : EReal) :
    (hi ≤ lo → b.setPossiblyTrue? lo hi = none) ∧
    (lo < hi → ∀ (d : ℝ) (PT PF : ℝ → Prop), b.Represents d PT PF →
      ∃ b', b.setPossiblyTrue? lo hi = some b' ∧
        b'.Represents d (fun t => PT t ∨ Covers d t lo hi) PF) := by -- --- PROOF ---
  refine ⟨fun h => by simp [FiniteKleeneSignalBuilder.setPossiblyTrue?,
    FiniteSignal.indicator?, h], fun hlh d PT PF hb => ?_⟩
  obtain ⟨hvalid, hdur, hts⟩ := hb
  -- the signal or'ed with the indicator of the interval, and what it says at every time
  obtain ⟨s', hs', hv, hd, hat⟩ :=
    (FiniteKleeneSignalBuilder.or_indicator_spec _ hvalid.1 lo hi).2 hlh
  obtain ⟨ind, hind, hc⟩ := Option.bind_eq_some_iff.mp hs'
  refine ⟨{ b with possiblyTrueSignal := s' },
    by simp [FiniteKleeneSignalBuilder.setPossiblyTrue?, hind, hc],
    ⟨hv, hvalid.2.1, by rw [hd]; exact hvalid.2.2⟩,
    by rw [hd]; exact hdur, fun t h0 h1 => ?_⟩
  obtain ⟨⟨x, hx, hxi⟩, ⟨y, hy, hyi⟩⟩ := hts t h0 h1
  obtain ⟨z, hz, hzi⟩ := hat t x hx h0 (hdur ▸ h1)
  exact ⟨⟨z, hz, by rw [hzi, hxi, hdur]⟩, ⟨y, hy, hyi⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
