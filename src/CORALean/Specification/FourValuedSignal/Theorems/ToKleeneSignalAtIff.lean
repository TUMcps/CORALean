module

public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalSpec

@[expose] public section

/-!
# The two Kleene refinements of a four-valued signal

Mapping inconclusive to `False` gives the signal that is `True` where the four-valued signal is
`True`, `False` where it is `False` or inconclusive; mapping it to `True` is the other way round.
`Unknown` is `Unknown` in both.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The two refinements, read off at each of the four values. -/
theorem FourValuedSignal.toKleeneSignal_at_iff (s : FourValuedSignal ℝ) (hs : s.IsValid) (t : ℝ)
    (ht : 0 ≤ t) : -- --- STMT ---
    ((s.toKleeneSignal Kleene.ff).at t = Kleene.tt ↔ s.at t = FourValued.tt) ∧
    ((s.toKleeneSignal Kleene.ff).at t = Kleene.ff ↔
      s.at t = FourValued.ff ∨ s.at t = FourValued.ii) ∧
    ((s.toKleeneSignal Kleene.ff).at t = Kleene.uu ↔ s.at t = FourValued.uu) ∧
    ((s.toKleeneSignal Kleene.tt).at t = Kleene.tt ↔
      s.at t = FourValued.tt ∨ s.at t = FourValued.ii) ∧
    ((s.toKleeneSignal Kleene.tt).at t = Kleene.ff ↔ s.at t = FourValued.ff) ∧
    ((s.toKleeneSignal Kleene.tt).at t = Kleene.uu ↔ s.at t = FourValued.uu) := by -- --- PROOF ---
  obtain ⟨h1, h2⟩ := (s.toKleeneSignal_spec hs Kleene.ff).2 t ht
  obtain ⟨g1, g2⟩ := (s.toKleeneSignal_spec hs Kleene.tt).2 t ht
  -- inconclusive is mapped to the given value, the others are read off
  by_cases hi : s.at t = FourValued.ii
  · rw [h1 hi, g1 hi, hi]
    simp
  · rw [h2 hi, g2 hi]
    generalize s.at t = k at hi ⊢
    cases k <;> first | exact absurd rfl hi | simp [FourValued.toKleene]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
