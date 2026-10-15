module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Definitions.Represents
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.KleeneSignal
public import CORALean.Specification.FiniteKleeneSignalBuilder.Theorems.Basic
public import CORALean.Specification.FiniteSignal.Theorems.CombineSpec

@[expose] public section

/-!
# What `kleeneSignal` computes

For a valid builder the three-valued signal is valid, has the builder's duration, and at every time
`t` of `[0,dur]` is `comb` of the two Boolean values there: true where only the property can be
true, false where it only can be false, unknown elsewhere.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteKleeneSignalBuilder.kleeneSignal?_spec (b : FiniteKleeneSignalBuilder) (d : ℝ)
    (PT PF : ℝ → Prop) (hb : b.Represents d PT PF) :
    ∃ s, b.kleeneSignal? = some s ∧ s.IsValid ∧ s.duration = d ∧ ∀ t : ℝ, 0 ≤ t → t ≤ d →
      ∃ v, s.at? t = some v ∧ (v = Kleene.tt ↔ PT t ∧ ¬ PF t) ∧
        (v = Kleene.ff ↔ PF t ∧ ¬ PT t) := by -- --- PROOF ---
  obtain ⟨hvalid, hdur, hts⟩ := hb
  obtain ⟨s, hs, hv, hd, hat⟩ :=
    FiniteSignal.combine?_spec FiniteKleeneSignalBuilder.comb _ _ hvalid.1 hvalid.2.1
  refine ⟨s, hs, hv, by rw [hd, ← hvalid.2.2, min_self, hdur], fun t h0 h1 => ?_⟩
  obtain ⟨⟨x, hx, hxi⟩, ⟨y, hy, hyi⟩⟩ := hts t h0 h1
  -- the two durations agree, so the combination is defined at every time up to it
  have hok : t < b.possiblyTrueSignal.duration ∧ t < b.possiblyFalseSignal.duration ∨
      b.possiblyTrueSignal.duration = b.possiblyFalseSignal.duration ∧
        t = b.possiblyTrueSignal.duration := by
    rcases lt_or_eq_of_le (hdur ▸ h1) with h | h
    · exact Or.inl ⟨h, by rw [← hvalid.2.2]; exact h⟩
    · exact Or.inr ⟨hvalid.2.2, h⟩
  refine ⟨_, hat t x y hx hy hok, ?_, ?_⟩
  · rw [FiniteKleeneSignalBuilder.comb_eq_tt_iff, ← hxi, ← hyi]
    simp
  · rw [FiniteKleeneSignalBuilder.comb_eq_ff_iff, ← hxi, ← hyi]
    simp [and_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
