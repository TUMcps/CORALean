module

public import CORALean.Specification.Kleene.Operations.Basic
public import CORALean.Specification.KleeneSignal.Definitions.IsValid
public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalSpec

@[expose] public section

/-!
# The two Boolean refinements of a three-valued signal

Mapping unknown to false gives the signal that is `true` where the three-valued signal is `True`;
mapping unknown to true gives the signal that is `true` where it is not `False`.

## Inputs
* `s` – three-valued signal
* `t` – time

## Hypotheses
* `hs` – the signal is valid
* `ht` – the time is nonnegative

## Conclusion
* the minimal refinement is true at true, the maximal except at false
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The minimal refinement is `true` at `True`, the maximal one except at `False`. -/
theorem KleeneSignal.toBoolSignal_at_iff (s : KleeneSignal ℝ) (hs : s.IsValid) (t : ℝ)
    (ht : 0 ≤ t) : -- --- CONCL ---
    ((s.toBoolSignal false).at t = true ↔ s.at t = Kleene.tt) ∧
      ((s.toBoolSignal true).at t = true ↔ s.at t ≠ Kleene.ff) := by -- --- PROOF ---
  obtain ⟨h1, h2⟩ := (KleeneSignal.toBoolSignal_spec s hs false).2 t ht
  obtain ⟨g1, g2⟩ := (KleeneSignal.toBoolSignal_spec s hs true).2 t ht
  -- unknown is false in the first, true in the second; the other values are read off
  by_cases hu : s.at t = Kleene.uu
  · rw [g1 hu, h1 hu, hu]
    exact ⟨iff_of_false (by decide) (by decide), iff_of_true rfl (by decide)⟩
  · rw [g2 hu, h2 hu]
    generalize s.at t = k at hu ⊢
    cases k <;> first | exact absurd rfl hu | simp [Kleene.toBool]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
